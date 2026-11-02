# RS^N³ · Hidrógeno

**El átomo de hidrógeno sobre los sitios enteros del cubo RS^N³.** La única forma de moverse es el
paso de eje, el `T_d` de cada eje (`D37`, `D39`); la celda del núcleo no lleva posición, solo un
estado; y ninguna cota depende de la celda `a` ni del tamaño de la caja. Lean 4 con Mathlib, sin
`sorry`, solo los axiomas `propext`, `Classical.choice` y `Quot.sound`.

Los `d` son la discretización de cada par posición–momento `(P_d, T_d)` de los tres ejes. El
teorema base satura solo en `d = 2, 3` y es estricto desde `d = 4` ([`nava-robertson-schrodinger`](https://github.com/naype888-cloud/nava-robertson-schrodinger),
`D22`, `D37`, `D39`); este repo lo usa y no lo repite.

## Resultados

### El modelo

| Enunciado | Lean |
|---|---|
| Los sitios son `p ∈ ℤ³`; la caja de semilado `M` sin la celda del núcleo | `cuboE` |
| Todo sitio distinto del núcleo está al menos a un paso: `a ≤ a·√(x²+y²+z²)` | `radiusE_ge` |
| La cinética es `⟨ψ, (6 − A) ψ⟩ / (2a²)`, con `A` la adyacencia de los saltos de eje | `kineticFull_eq` |
| Esa `A` es la del grafo `pathGraph dx □ (pathGraph dy □ pathGraph dz)` de `D37` | `adjForm_boxSet`, `kineticFull_boxSet` (`Caja.lean`) |
| …y es `ρₓTₓ + ρ_yT_y + ρ_zT_z`: la forma cuadrática del transporte de cada eje | `Puente.form_cube` (`Puente/D50g.lean`, dentro del corpus) |

### Hardy y la energía de la caja

| Enunciado | Lean |
|---|---|
| Hardy desde un campo sobre las aristas, sin celda ni tamaño | `edge_vf`, `hardy_vf` |
| El peso del campo `κ = (1/4) m / (m² + q + 1)` es `≥ 1/(4r²)` fuera del núcleo (cuerda por eje y un polinomio en una variable con coeficientes positivos) | `fax_eq`, `chord1`, `chord2`, `sum_phi`, `one_var`, `weight_ge` |
| **Hardy en los sitios enteros:** `(1/4) Σ ψ²/r² ≤ Σ aristas (Δψ)²`, para todo soporte finito con `ψ(núcleo) = 0` | `hardy_entero` |
| La energía de toda caja es `≥ −2k²`, para toda celda `a` y toda `M` | `energyE_ge_hardy`, `le_groundE_hardy` |
| También `≥ −k/a`, porque el sitio más cercano está a `a` | `energyE_ge`, `le_groundE` |
| Un solo sitio junto al núcleo da energía `3/a² − k/a`: cota superior | `energyE_trial`, `groundE_le_trial` |

### El límite: las cajas convergen y no se alcanza

| Enunciado | Lean |
|---|---|
| Crecer la caja solo baja la energía fundamental | `groundE_succ_le`, `levelsE_antitone` |
| Converge a su ínfimo `E∞`, y cada caja finita queda por encima | `tendsto_levelsE`, `limitE_le_levels` |
| `E∞` entre `max(−2k², −k/a)` y `3/a² − k/a` | `limitE_bounds` |

### Escala y velocidad

| Enunciado | Lean |
|---|---|
| El tope del cubo `2ta/ħ = ħ/(ma)` es `c` exactamente en la longitud de Compton reducida, `= α·a₀` | `cap_eq_c_iff`, `compton_eq_alpha_bohr` |
| La velocidad de Bohr es `α c`; el 1s anda a la fracción `α` del tope | `bohr_speed`, `bohr_speed_over_cap` |
| `‖vᵢψ‖ ≤ 2ta·‖ψ‖ = ‖ψ‖/a` en cualquier caja y a lo largo de cualquier eje | `vel_bound`, `vel_bound_cube`, `vel_bound_cuboE` |
| A escala de Compton, el sitio más cercano tiene energía de Coulomb `α m c²` | `coulomb_nearest_at_compton` |
| El radio de Bohr mide `1/α` pasos | `bohr_in_steps` |

### El primer paso del álgebra: la bola de Bloch (`d = 2`)

El par `(T, P) = (σₓ, σ_z)` es la fila 21 de la tabla de pares del teorema base (`(P₂, T₂)`). Para
el estado `ρ = ½(1 + xσₓ + yσ_y + zσ_z)`:

| Enunciado | Lean |
|---|---|
| El vector de Bloch es la tripleta de esperanzas de las Pauli | `ex_sx`, `ex_sy`, `ex_sz` |
| El defecto de Robertson–Schrödinger del par es `1 − (x² + y² + z²)` | `defect_eq` |
| La relación de incertidumbre es exactamente la bola: `‖v‖ ≤ 1` | `defect_nonneg_iff` |
| Se satura exactamente en la esfera, los estados puros | `defect_eq_zero_iff` |
| `ρ ≥ 0` si y solo si `‖v‖ ≤ 1` | `posSemidef_rho_iff` |

### Hasta dónde cierra el álgebra: `d = 2, 3`

El hop de la cadena es `T = S + Sᵀ` (`S` el desplazamiento) y `P` la posición `0, 1, …, d − 1`.

| Enunciado | Lean |
|---|---|
| `T` es la adyacencia del grafo camino de `d` posiciones | `Tp_eq_adj` |
| `[T, P] = Sᵀ − S` y `[P, [T, P]] = −T`, para todo `d` | `br_Tp_Pp`, `br_Pp_br_Tp_Pp` |
| `[T, [T, P]] = diag(−2, 0, …, 0, 2)`, un operador de frontera | `dbl_eq` |
| Es combinación de `P` y `1` si y solo si `d ≤ 3`: `{T, P, [T, P], 1}` cierra en `d = 2, 3` y no desde `d = 4` | `closes_iff` |

La frontera coincide con la de `saturada_TdPd_iff` (`D22`): el teorema base satura solo en
`d = 2, 3`. Este repo no prueba la relación entre ambos enunciados.

## Lo que no está probado

- Que `E∞` sea el nivel de Rydberg.
- La identificación de `(T_d, P_d)`, para `d = 2, 3`, con las matrices de espín `1/2` y `1`, y la
  relación formal entre el cierre del álgebra y la saturación de Robertson.
- Que `1/4` sea la mejor constante de `hardy_entero`: está probada como cota, no como óptima.
- El amarre en Lean de `evaluacionTdPd 2` (corpus, `D22`) con `BolaDeBloch.lean`. Para todo
  `d ≥ 2` el corpus ya prueba la saturación y el defecto (`saturada_TdPd_iff`,
  `defectoIntrinseco_TdPd_eq_defectoGram`, `D39`).
- El origen de `ℤ³` en la celda del núcleo es una convención de este repo, no un enunciado del
  teorema base.

## Construir

```
lake build
tools/verificar.sh      # además compila Puente/D50g.lean dentro del corpus
```

Solo Mathlib `v4.35.0` (Lean `4.35.0`). `Puente/D50g.lean` importa el corpus
([`nava-robertson-schrodinger`](https://github.com/naype888-cloud/nava-robertson-schrodinger)) y se
compila dentro de él: `cd nava-robertson-schrodinger && lake env lean ../nrs3-hidrogeno/Puente/D50g.lean`.

**Historia.** Los commits anteriores a «Retira el modelo con medias celdas» usan celdas con centro en
`(i + ½)a` y la cota `E₀ ≥ −10k²`. Ese modelo está retirado: no hay distancia menor a un paso. Los
archivos que lo contenían ya no están en el árbol.

## Línea de tiempo 1911–1945

| Año | Evento | Aquí |
|---|---|---|
| 1913 | Bohr: el átomo y su radio | `bohr` |
| 1916 | Sommerfeld: la constante de estructura fina | `alpha` |
| 1920 | Hardy: su desigualdad | `hardy_entero` |
| 1929–30 | Robertson y Schrödinger: la desigualdad de incertidumbre | `defect_eq` |

**Antecedentes y herramientas fuera de la ventana.** Fiedler (1973), Lean 4 y Mathlib.

## El mosaico

- [RS^N y RS^N³ — el teorema base](https://github.com/naype888-cloud/nava-robertson-schrodinger)
- [RS^N³ · Mandelstam–Tamm y Cramér–Rao](https://github.com/naype888-cloud/nrs3-mandelstam-tamm-cramer-rao)
- [RS^N³ · Landauer y Carnot](https://github.com/naype888-cloud/nrs3-landauer-carnot)
- [RS^N³ · de Sitter](https://github.com/naype888-cloud/nrs3-de-sitter)
- [RS^N³ · Penrose](https://github.com/naype888-cloud/nrs3-penrose) (propuesta)
- [RS^N³ · Pauli–Dirac](https://github.com/naype888-cloud/nrs3-pauli-dirac)
- [RS^N³ · El cono de la incertidumbre](https://github.com/naype888-cloud/nrs3-uncertainty-cone)
- [RS^N³ · Poincaré](https://github.com/naype888-cloud/nrs3-poincare)
- [RS^N³ · Defecto y curvatura](https://github.com/naype888-cloud/nrs3-defect-curvature)
- [RS^N³ · Rovelli — Loop Quantum Gravity](https://github.com/naype888-cloud/nrs3-rovelli-lqg) (propuesta)
- [RS^N³ · Dark](https://github.com/naype888-cloud/nrs3-dark)
- [RS^N³ · Cristales](https://github.com/naype888-cloud/nrs3-cristales)
- **[RS^N³ · Hidrógeno](https://github.com/naype888-cloud/nrs3-hidrogeno)** (este)

## Licencia

NRS Noncommercial License 1.0.0, ver [`LICENSE`](LICENSE). Autor: Eduardo Nava-Hernandez.
