import sys
import shutil
from os import listdir

def fmt(src):
    data = []
    shutil.copyfile(src, src + ".bak")

    with open(src, "r") as f:
        values = []
        block_values = []
        block_name = None
        name = None
        for l in f:
            if l[0].isalpha():
                if block_name is not None and len(block_values) != 0:
                    block_values = sorted(block_values, key=lambda v: v[0].lower())
                    values.append((block_name, block_values))
                if name is not None:
                    data.append((name, values))
                values = []
                block_values = []
                block_name = l.split(":")[0].strip()
                name = l.split(":")[0].strip()
            elif l.strip() != "":
                l = l.strip()
                if l[0] == "#":
                    

                    if block_name is not None and len(block_values) != 0:
                        block_values = sorted(block_values, key=lambda v: v[0].lower())
                        values.append((block_name, block_values))
                    block_name = l
                    block_values = []
                else:
                    key, value = l.rsplit(":", 1)
                    block_values.append((key.strip(), value.strip()))
        if block_name is not None and len(block_values) != 0:
            block_values = sorted(block_values, key=lambda v: v[0].lower())
            values.append((block_name, block_values))
        if name is not None:
            data.append((name, values))

    out = ""
    for (k, v) in data:
        out += k + ":\n"
        for (block_name, block_values) in v:
            if block_name.startswith("#"):
                out += "\n  " + block_name + "\n"
            for (key, val) in block_values:
                out += "  " + key + ": " + val + "\n"
        out += "\n"

    with open(src, "w") as f:
        f.write(out)

srcs = ["./symbols/" + x for x in listdir("./symbols") if x.endswith(".yml")]
for src in srcs:
    fmt(src)

