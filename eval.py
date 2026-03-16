import sys

s = open(sys.argv[1]).read()

L = []
for x in s.split("\n"):
    if x.startswith("Best"):
        opti = x[x.find("(")+1:x.find(")")]
        for l in L:
            c = l[l.find("cost=")+5:l.find(",")]
            if c == opti:
                print(l)
                break
        L = []
    if x.startswith("#"):
        L.append(x)
