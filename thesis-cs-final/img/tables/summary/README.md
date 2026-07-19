# Souhrnné tabulky

Tato složka obsahuje tabulky určené hlavně pro experimentální kapitolu diplomové práce.

- `best_total_d4.csv` – nejlepší konfigurace pro každý problém podle celkového času `nástroj + d4`.
- `best_total_kissat.csv` – nejlepší konfigurace pro každý problém podle celkového času `nástroj + kissat`.
- `best_solver_d4.csv` – nejlepší konfigurace podle samotného času solveru d4.
- `best_solver_kissat.csv` – nejlepší konfigurace podle samotného času solveru kissat.
- `best_model_reduction.csv` – konfigurace s největší redukcí počtu modelů.
- `method_wins.csv` – počty vítězství jednotlivých množin permutací pro různé metriky.
- `method_geomean.csv` – geometrické průměry zrychlení a redukce modelů podle množiny permutací.
- `timeout_summary.csv` – přehled timeoutů podle problému a množiny permutací.
- `problem_overview.csv` – jedna souhrnná řádka pro každý problém.

Poznámka: geometrický průměr se počítá pouze z kladných konečných hodnot a nebere v úvahu řádky `k=0`, protože ty slouží jako baseline.
