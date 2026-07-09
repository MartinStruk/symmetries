from pysat.formula import CNF
import itertools
import random
import argparse
from itertools import combinations

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

# fromule pro problém nalezení matice s řádky a sloupci se zadanými součty
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

# latinské čtverce
def latinsq(n):
    def var(r, c, v):        
        return v * n * n + r * n + c + 1

    clauses = []

    # právě jedna hodnota na každém místě
    for r in range(n):
        for c in range(n):
            # alespoň jedna
            clauses.append([var(r, c, v) for v in range(n)])

            # nejvýše jedna
            for v1 in range(n):
                for v2 in range(v1 + 1, n):
                    clauses.append([
                        -var(r, c, v1),
                        -var(r, c, v2)
                    ])

    # každá hodnota se objeví právě jednou v každém řádku
    for r in range(n):
        for v in range(n):
            # alespoň jednou
            clauses.append([var(r, c, v) for c in range(n)])

            # nejvýše jednou
            for c1 in range(n):
                for c2 in range(c1 + 1, n):
                    clauses.append([
                        -var(r, c1, v),
                        -var(r, c2, v)
                    ])

    # každá hodnota se objeví právě jendou v každém sloupci
    for c in range(n):
        for v in range(n):
            # alespoň jednou
            clauses.append([var(r, c, v) for r in range(n)])

            # nejvýše jednou
            for r1 in range(n):
                for r2 in range(r1 + 1, n):
                    clauses.append([
                        -var(r1, c, v),
                        -var(r2, c, v)
                    ])

    return clauses

# problém společenských golfistů
def golf(g, ppg, w):
    n = g * ppg  

    clauses = []

    def var(week, player, group):
        return week * n * g + player * g + group + 1

    # každý hráč v právě jedné skupině každý týden
    for week in range(w):
        for player in range(n):
            # alespoň jedna skupina
            clauses.append([var(week, player, group) for group in range(g)])

            # nejvýše jedna skupina
            for g1 in range(g):
                for g2 in range(g1 + 1, g):
                    clauses.append([-var(week, player, g1), -var(week, player, g2)])

    # každá skupina má právě ppg hráčů každý týden
    for week in range(w):
        for group in range(g):
            players = [var(week, i, group) for i in range(n)]

            # alespoň ppg hráčů
            for subset in combinations(players, n - ppg + 1):
                clauses.append(list(subset))

            # nejvýše ppg hráčů
            for subset in combinations(players, ppg + 1):
                clauses.append([-v for v in subset])

    # žádný pár se nepotká dvakrát
    for i in range(n):
        for j in range(i + 1, n):
            for w1 in range(w):
                for w2 in range(w1 + 1, w):
                    for g1 in range(g):
                        for g2 in range(g):
                            clauses.append([-var(w1, i, g1), -var(w1, j, g1), -var(w2, i, g2), -var(w2, j, g2)])

    return clauses

def main():
    parser = argparse.ArgumentParser(description = "Možnosti pro vstupní argumenty:", formatter_class=argparse.RawTextHelpFormatter)

    parser.add_argument("pigeons", type=int, help="Počet holubů pro problém holubníku")

    parser.add_argument("holes", type=int, help="Počet holubníků pro problém holubníku")

    parser.add_argument("n", type=int, help="Hodnota n pro problém n královen (N-queens)")

    parser.add_argument("rc", type=int, help="Počet řádků a sloupců pro náhodně generované hodnoty pro problém nalezení matice s řádky a sloupci se zadanými součty \nAby byl celkový součet ve všech řádcích roven celkovému součtu ve všech sloupcích, přidá se buď jeden řádek navíc, nebo jeden sloupec navíc")
    
    parser.add_argument("rcrand", type=int, help="Maximální hodnota, která se může náhodně vygenerovat pro součet v konkrétním řádku nebo sloupci")
    
    parser.add_argument("lsq", type=int, help="Rozměr matice pro problém latinských čtverců")
    
    parser.add_argument("g", type=int, help="Počet skupin pro problém společenských golfistů")
    
    parser.add_argument("p", type=int, help="Počet hráčů pro problém společenských golfistů")
    
    parser.add_argument("w", type=int, help="Počet týdnů pro problém společenských golfistů")

    args = parser.parse_args()

    pig = args.pigeons
    hol = args.holes
    n = args.n
    lsq = args.lsq
    g = args.g
    p = args.p
    w = args.w
    
    # data o součtech a předání dat na vstup
    rtotal = 0
    ctotal = 0
    rsums = []
    csums = []
    # generování náhodných hodnot pro součty
    for _ in range(args.rc):
        rrand = random.randint(0,args.rcrand)
        crand = random. randint(0,args.rcrand)
        rtotal += rrand
        rsums.append(rrand)
        ctotal += crand
        csums.append(crand)
    if rtotal > ctotal:
        csums.append(rtotal-ctotal)
    else:
        rsums.append(ctotal-rtotal)
    
    sumdata = ""
    for i in range(len(rsums)):
        if i != 0: sumdata += ','
        sumdata += str(rsums[i])    
    sumdata += '|'
    for j in range(len(csums)):
        if j != 0: sumdata += ','
        sumdata += str(csums[j])
    
    # uložení do příslušného souboru společně s informacemi navíc v komentářích
    # (počet řádků/sloupců matice a typ symetrie)
    cnfp = CNF(from_clauses=phpformula(pig,hol))
    cnfq = CNF(from_clauses=nqueens(n))
    cnfrc = CNF(from_clauses=rcsums(rsums,csums))
    cnflsq = CNF(from_clauses=latinsq(lsq))
    cnfg = CNF(from_clauses=golf(g,p,w))
    
    with open("inputphp.cnf", "w") as f:
        f.write(f"c {pig} {hol} rc\n")
        f.write(f"c pig{pig}_hol{hol}\n")
        cnfp.to_fp(f)
    
    with open("inputqueens.cnf", "w") as f:
        f.write(f"c {n} {n} d\n")
        f.write(f"c n{n}\n")
        cnfq.to_fp(f)
        
    with open("inputrcsums.cnf", "w") as f:
        f.write(f"c {len(rsums)} {len(csums)} sums{sumdata}\n")
        f.write(f"c rc{args.rc}_rcrand{args.rcrand}\n")
        cnfrc.to_fp(f)

    with open("inputlatinsq.cnf", "w") as f:
        f.write(f"c {lsq*lsq} {lsq} rc3d{lsq}\n")
        f.write(f"c lsq{lsq}\n")
        cnflsq.to_fp(f)

    with open("inputgolf.cnf", "w") as f:
        f.write(f"c {p*w*g} {g} rc3d{p*g}\n")
        f.write(f"c g{g}_p{p}_w{w}\n")
        cnfg.to_fp(f)
        
if __name__ == "__main__":
    main()