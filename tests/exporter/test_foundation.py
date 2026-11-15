#!/usr/bin/env python3
"""Fresh compiler captures for the finite foundation format (pinned toolchain required)."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]

class FoundationExport(unittest.TestCase):
    def export(self, root, destination):
        return subprocess.run([
            "bash", "tools/export-mir.sh", "--output", str(destination),
            "--foundation", "--root", root, "--", "exporter/fixtures/foundation.rs",
            "--crate-type=lib", "--crate-name", "foundation",
        ], cwd=ROOT, capture_output=True, text=True)

    def test_generic_templates_and_concrete_array(self):
        with tempfile.TemporaryDirectory(prefix="foundation-") as directory:
            for root in ("identity", "array_identity", "concrete", "link_identity"):
                output = Path(directory) / f"{root}.json"
                result = self.export(root, output)
                self.assertEqual(result.returncode, 0, result.stderr)
                doc = json.loads(output.read_text())
                self.assertEqual((doc["schema"], doc["schema_version"]), ("lean-miri-foundation", 1))
                self.assertEqual(len(doc["bodies"]), 1)
                self.assertFalse(any(key.startswith("compiler_") for key in doc))
                shapes = [node["shape"] for node in doc["types"]]
                if root == "identity":
                    self.assertIn({"kind":"param", "index":0, "name":"T"}, shapes)
                if root == "array_identity":
                    array = next(s for s in shapes if s["kind"] == "array")
                    self.assertEqual(array["length"], {"kind":"param", "index":1, "name":"N"})
                    params = doc["bodies"][0]["environment"]["parameters"]
                    self.assertEqual([(p["kind"], p["index"]) for p in params], [("type",0),("const",1)])
                if root == "concrete":
                    array = next(s for s in shapes if s["kind"] == "array")
                    self.assertEqual(array["length"]["bits"], "3")
                value = doc["bodies"][0]["blocks"][0]["statements"][0]["value"]
                self.assertTrue(value["retag"])
                if root == "link_identity":
                    definitions = [d for d in doc["definitions"] if "adt" in d]
                    self.assertEqual(len(definitions), 1)
                    self.assertEqual(len(definitions[0]["adt"]["variants"][0]["fields"]), 2)
                    self.assertLess(len(doc["types"]), 10)
                    self.assertNotIn(None, doc["types"])

    def test_unsupported_call_and_missing_root_abort(self):
        with tempfile.TemporaryDirectory(prefix="foundation-") as directory:
            for root, diagnostic in (("calls", "unsupported terminator"), ("missing", "missing MIR root")):
                output = Path(directory) / f"{root}.json"
                result = self.export(root, output)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)
                self.assertFalse(output.exists())

if __name__ == "__main__":
    unittest.main()
