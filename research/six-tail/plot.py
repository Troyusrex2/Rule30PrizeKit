"""Regenerate the explanatory figure from the independently checked certificate."""
import json
from pathlib import Path
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
record = next(r for r in json.loads((HERE / "certificates.json").read_text()) if r["word"] == "110001")
counts = [len(s) for s in reversed(record["predecessor_sets"])]
plt.rcParams.update({"svg.fonttype": "none", "svg.hashsalt": "Rule30SixTail"})
fig, ax = plt.subplots(figsize=(7.8, 3.8), layout="constrained")
ax.plot(range(len(counts)), counts, marker="o", color="#176b91", linewidth=2)
ax.axvline(6, color="#666666", linestyle="--", linewidth=1)
ax.annotate("6 tail steps reversed", xy=(6, counts[6]), xytext=(0.6, 61),
            arrowprops={"arrowstyle": "->", "color": "#666666"}, fontsize=10)
ax.annotate("Empty after 14 additional white steps", xy=(20, 0), xytext=(8, 50),
            arrowprops={"arrowstyle": "->", "color": "#666666"}, fontsize=10)
ax.set(xlabel="Steps backward from the all-white endpoint", ylabel="Possible strip states",
       title="Backward obstruction for 110001 at width 14", xticks=range(0, 21, 2), ylim=(-2, 76))
ax.spines[["top", "right"]].set_visible(False)
ax.grid(axis="y", alpha=.2)
fig.savefig(HERE / "backward-obstruction.png", dpi=160)
svg = HERE / "backward-obstruction.svg"
fig.savefig(svg, metadata={"Date": None})
svg.write_text("\n".join(line.rstrip() for line in svg.read_text().splitlines()) + "\n",
               encoding="utf-8", newline="\n")
