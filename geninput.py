# %%
from pysat.formula import CNF
import itertools

# formule pro pigeon hole principle problém
def phpformula(p, h):
    clauses = []

    # každý holub v alespoň jednom holubníku
    for i in range(1,p+1):
        clause = []
        for j in range(1,h+1):
            clause.append((i-1)*h+j)
        clauses.append(clause)

    # v každém holubníku nejvýše jeden holub
    for i in range(1,h+1):
        for j in range(1,p+1):
            for k in range(j+1,p+1):
                clauses.append([-(j-1)*h-i,-(k-1)*h-i])

    return clauses

# formule pro N-queens problém
def nqueens(n):
    clauses = []

    def var(r, c):
        return r * n + c + 1

    # klauzule pro řádky
    for r in range(n):
        # alespoň jedna
        clauses.append([var(r, c) for c in range(n)])

        # nejvýše jedna
        for c1 in range(n):
            for c2 in range(c1 + 1, n):
                clauses.append([-var(r, c1), -var(r, c2)])

    # klauzule pro sloupce
    for c in range(n):
        # alespoň jedna
        clauses.append([var(r, c) for r in range(n)])

        # nejvýše jedna
        for r1 in range(n):
            for r2 in range(r1 + 1, n):
                clauses.append([-var(r1, c), -var(r2, c)])

    # klauzule pro diagonály směrem (↘) a nejvýše jedna
    for d in range(-(n - 1), n):
        diag = [(r, r - d) for r in range(n) if 0 <= r - d < n]
        for i in range(len(diag)):
            for j in range(i + 1, len(diag)):
                r1, c1 = diag[i]
                r2, c2 = diag[j]
                clauses.append([-var(r1, c1), -var(r2, c2)])

    # klauzule pro diagonály směrem (↗) a nejvýše jedna
    for s in range(2 * n - 1):
        diag = [(r, s - r) for r in range(n) if 0 <= s - r < n]
        for i in range(len(diag)):
            for j in range(i + 1, len(diag)):
                r1, c1 = diag[i]
                r2, c2 = diag[j]
                clauses.append([-var(r1, c1), -var(r2, c2)])

    return clauses

import itertools

# fromule pro problém najít matici se řádky a sloupci se zadaným součtem
def rcsums(row_sums, col_sums):
    m = len(row_sums)
    n = len(col_sums)

    assert sum(row_sums) == sum(col_sums), \
        "Celkový součet řádku se musí rovnat celkovému součtu sloupců"

    clauses = []

    def var(r, c):
        return r * n + c + 1

    # klauzule pro řádky
    for r in range(m):
        cells = [var(r, c) for c in range(n)]
        k = row_sums[r]

        # alespoň k
        if k > 0:
            for subset in itertools.combinations(cells, n - k + 1):
                clauses.append(list(subset))

        # nejvýše k
        if k < n:
            for subset in itertools.combinations(cells, k + 1):
                clauses.append([-v for v in subset])

    # klauzule pro sloupce
    for c in range(n):
        cells = [var(r, c) for r in range(m)]
        k = col_sums[c]

        # alespoň k
        if k > 0:
            for subset in itertools.combinations(cells, m - k + 1):
                clauses.append(list(subset))

        # nejvýše k
        if k < m:
            for subset in itertools.combinations(cells, k + 1):
                clauses.append([-v for v in subset])

    return clauses

# parametry pro jednotlivé problémy
pig = 40
hol = 39

n = 100

rsums = [1,2,3,4,5]
csums = [2,2,2,2,2,2,2,1]

# uložení do příslušného souboru společně s informacemi navíc v komentářích
# (počet řádků/sloupců matice a typ symetrie)
cnfp = CNF(from_clauses=phpformula(pig,hol))
cnfq = CNF(from_clauses=nqueens(n))
cnfrc = CNF(from_clauses=rcsums(rsums,csums))

with open("inputphp.cnf", "w") as f:
    f.write(f"c {pig} {hol} rc\n")
    cnfp.to_fp(f)

with open("inputqueens.cnf", "w") as f:
    f.write(f"c {n} {n} rc\n")
    cnfq.to_fp(f)
    
with open("inputrcsums.cnf", "w") as f:
    f.write(f"c {len(rsums)} {len(csums)} rc\n")
    cnfrc.to_fp(f)

# %%



