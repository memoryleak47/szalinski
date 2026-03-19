import sys
import re
import matplotlib.pyplot as plt
import numpy as np

FACTOR = "cost"
# choose "cost", "memo-size", "time"

def parse_costs(filename):
    with open(filename, 'r') as f:
        # Extracts only numeric values for cost to avoid trailing characters
        return [float(x) for x in re.findall(rf"{FACTOR}=([\d.]+)", f.read())]

if len(sys.argv) < 3:
    print("Usage: python plot.py <file1> <file2>")
    sys.exit(1)

file1, file2 = sys.argv[1], sys.argv[2]
costs1 = parse_costs(file1)
costs2 = parse_costs(file2)

indices = np.arange(len(costs1))
width = 0.35

plt.figure(figsize=(12, 6))
plt.bar(indices - width/2, costs1, width, label=file1)
plt.bar(indices + width/2, costs2, width, label=file2)

plt.xlabel('Benchmark Problem')
plt.ylabel(FACTOR)
plt.title(f'{FACTOR} Comparison')
plt.xticks(indices)
plt.legend()
plt.grid(axis='y', linestyle='--', alpha=0.7)
plt.tight_layout()
plt.show()
