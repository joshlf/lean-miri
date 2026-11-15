//! Finite declaration source for Fn-family vtable candidate construction.
//! Never calls vtable_entries, object-safety, instance selection or allocation.
use super::*;
use std::collections::HashSet;

impl<'tcx> Material<'tcx> {
    fn fn_vtable_type(&mut self, tcx: TyCtxt<'tcx>, value: ty::Ty<'tcx>) -> Result<Value> {
        Ok(match *value.kind() {
            ty::Param(p) => json!({"kind":"param","index":p.index}),
            ty::Tuple(elements) => json!({"kind":"tuple","elements":elements.iter().map(|t|self.fn_vtable_type(tcx,t)).collect::<Result<Vec<_>>>()?}),
            ty::Ref(region,pointee,mutable) => {
                let region = match region.kind() {
                    ty::ReBound(ty::BoundVarIndexKind::Bound(index), variable) => json!({"kind":"bound","binder":index.as_u32(),"variable":variable.var.as_u32(),"source_kind":format!("{:?}",variable.kind)}),
                    ty::ReErased => json!({"kind":"erased"}),
                    ty::ReStatic => json!({"kind":"static"}),
                    other => return unsupported("Fn declaration reference region",other),
                };
                json!({"kind":"reference","mutable":mutable.is_mut(),"region":region,"pointee":self.fn_vtable_type(tcx,pointee)?})
            },
            ty::Alias(rigid, alias) => match alias.kind {
                ty::AliasTyKind::Projection {def_id} => json!({"kind":"projection","rigid":format!("{rigid:?}"),"definition":self.definition(tcx,def_id),"arguments":self.fn_vtable_arguments(tcx,alias.args)?}),
                other => return unsupported("Fn declaration alias",other),
            },
            other => return unsupported("Fn declaration type",other),
        })
    }
    fn fn_vtable_arguments(&mut self, tcx: TyCtxt<'tcx>, args: ty::GenericArgsRef<'tcx>) -> Result<Vec<Value>> {
        args.iter().map(|arg|match arg.kind() {
            ty::GenericArgKind::Type(value) => Ok(json!({"kind":"type","type":self.fn_vtable_type(tcx,value)?})),
            other => unsupported("Fn declaration generic argument",other),
        }).collect()
    }
    pub(super) fn fn_vtable_source(&mut self, tcx: TyCtxt<'tcx>) -> Result<Value> {
        let roots = [("fn",tcx.lang_items().fn_trait()),("fn_mut",tcx.lang_items().fn_mut_trait()),("fn_once",tcx.lang_items().fn_once_trait())];
        let root_records = roots.iter().map(|(kind,definition)|json!({"kind":kind,"definition":definition.map(|d|self.definition(tcx,d))})).collect::<Vec<_>>();
        let mut pending = roots.iter().filter_map(|(_,d)|*d).collect::<Vec<_>>();
        let mut seen = HashSet::new();
        let mut declarations = Vec::new();
        while let Some(definition) = pending.pop() {
            if !seen.insert(definition) {continue;}
            if definition.is_local() || tcx.crate_name(definition.krate).as_str() != "core" {
                return unsupported("non-pinned core Fn source",definition);
            }
            let generics = tcx.generics_of(definition);
            let lang_item = roots.iter().find_map(|(kind,d)|(*d == Some(definition)).then_some(*kind))
                .unwrap_or_else(|| if tcx.is_lang_item(definition,rustc_attr_ir::LangItem::MetaSized) {"meta_sized"}
                    else if tcx.is_lang_item(definition,rustc_attr_ir::LangItem::PointeeSized) {"pointee_sized"} else {"other"});
            let supers = tcx.explicit_super_clauses_of(definition);
            let mut super_clauses = Vec::new();
            for (clause,_) in supers.skip_binder() {
                let bound = clause.kind();
                if let ty::ClauseKind::Trait(predicate) = bound.skip_binder() {
                    let reference = predicate.trait_ref;
                    pending.push(reference.def_id);
                    super_clauses.push(json!({"kind":"trait","definition":self.definition(tcx,reference.def_id),
                        "arguments":self.fn_vtable_arguments(tcx,reference.args)?,"polarity":format!("{:?}",predicate.polarity),
                        "bound_variables":bound.bound_vars().iter().map(|v|format!("{v:?}")).collect::<Vec<_>>()}));
                } else {
                    // prepare_vtable_segments filters non-Trait source clauses.
                    super_clauses.push(json!({"kind":"non_trait","source":format!("{clause:?}")}));
                }
            }
            let mut associated = Vec::new();
            for item in tcx.associated_items(definition).in_definition_order() {
                let mut record = json!({"definition":self.definition(tcx,item.def_id),"name":item.name().as_str(),
                    "kind":match item.kind {ty::AssocKind::Fn{..}=>"method",ty::AssocKind::Type{..}=>"type",ty::AssocKind::Const{..}=>"const"}});
                if item.is_fn() {
                    let signature = tcx.fn_sig(item.def_id).instantiate_identity().skip_normalization();
                    let raw = signature.skip_binder();
                    let params = tcx.generics_of(item.def_id);
                    let own_clauses = tcx.explicit_clauses_of(item.def_id);
                    record["method"] = json!({"is_method":item.is_method(),"final":item.defaultness(tcx).is_final(),
                        "parent_count":params.parent_count,"own_parameters":params.own_params.iter().map(|p|format!("{:?}",p.kind)).collect::<Vec<_>>(),
                        "own_clauses":own_clauses.clauses.iter().map(|(c,_)|format!("{c:?}")).collect::<Vec<_>>(),
                        "bound_variables":signature.bound_vars().iter().map(|v|format!("{v:?}")).collect::<Vec<_>>(),
                        "safety":format!("{:?}",raw.safety()),"abi":format!("{:?}",raw.abi()),"variadic":raw.c_variadic(),
                        "inputs":raw.inputs().iter().map(|t|self.fn_vtable_type(tcx,*t)).collect::<Result<Vec<_>>>()?,
                        "output":self.fn_vtable_type(tcx,raw.output())?});
                }
                associated.push(record);
            }
            declarations.push(json!({"definition":self.definition(tcx,definition),"core_source":true,"lang_item":lang_item,"has_self":generics.has_self,
                "parameters":generics.own_params.iter().map(|p|match p.kind {ty::GenericParamDefKind::Type{has_default,..}=>json!({"index":p.index,"kind":"type","has_default":has_default}),_=>json!({"index":p.index,"kind":"unsupported","source":format!("{:?}",p.kind)})}).collect::<Vec<_>>(),
                "super_clauses":super_clauses,"associated_items":associated}));
        }
        Ok(json!({"roots":root_records,"declarations":declarations,"no_trait_vptr":tcx.sess.opts.unstable_opts.no_trait_vptr}))
    }
}
