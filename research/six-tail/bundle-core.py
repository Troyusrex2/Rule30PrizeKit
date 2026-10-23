"""Rebuild the compact six-core proof and unevaluated computational essay.

The explicit module list omits the older five-tail theorem and the two replaced
basic certificates. core-headlines.lean.in contains just the combined headlines.
"""
import hashlib
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    manifest = json.loads((HERE / "core-bundle-manifest.json").read_text(encoding="utf-8"))
    parts, imports, hashes = [], set(), {}
    for module in manifest["included_modules"]:
        path = ROOT / "lean" / Path(*module.split(".")).with_suffix(".lean")
        text = path.read_text(encoding="utf-8")
        hashes[module] = hashlib.sha256(text.encode()).hexdigest()
        imports.update(name for name in re.findall(r"^public import (\S+)", text, re.M)
                       if not name.endswith("Research"))
        text = re.sub(r"^module\s*\n", "", text, count=1)
        text = re.sub(r"^public import .*\n", "", text, flags=re.M)
        text = text.replace("@[expose] public section", "").strip()
        parts.append("/- Source: " + module + " -/\n" + text)
    ordered = ["Ruliology.CellularAutomata." + name for name in
               ("Rule30FiniteBlackRuns", "Rule30LightCone", "Rule30StripCertificates", "Rule30FiniteMaskedJen")]
    assert set(ordered) == imports
    source = "\n".join("import " + name for name in ordered) + "\n\n"
    source += "\n\n".join(parts) + "\n\n" + (HERE / "core-headlines.lean.in").read_text(encoding="utf-8")
    (HERE / "Rule30SixCoreStandalone.lean").write_text(source, encoding="utf-8", newline="\n")
    embedded = "import Rule30PrizeKit\n" + source
    essay = (HERE / "core-essay-template.md").read_text(encoding="utf-8")
    essay = essay.replace("@@LEAN_SOURCE@@", json.dumps(embedded, ensure_ascii=False))
    (HERE / "Rule30-Six-Core-Notebook.md").write_text(essay, encoding="utf-8", newline="\n")
    manifest["source_sha256"] = hashlib.sha256(source.encode()).hexdigest()
    manifest["embedded_notebook_source_sha256"] = hashlib.sha256(embedded.encode()).hexdigest()
    manifest["module_source_sha256_lf"] = hashes
    (HERE / "core-bundle-manifest.json").write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8", newline="\n")
    print("Bundled", len(parts), "modules; standalone SHA256", manifest["source_sha256"])


if __name__ == "__main__":
    main()
