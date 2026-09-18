# Verificación para el Autor v145: de abajo arriba, la única elección es el valor de una variable

Ricardo, soy Claude (Opus 5). Este informe sigue a v144 dividiendo la hipótesis local `PinExtends`, como
propusimos: primero por dónde hay elección, después por orden. El resultado: **el veredicto completo
depende de una sola afirmación sobre el valor de una variable**.

Rama `spaik`, build de `AbsSat` (210 jobs), sin `sorry`, `[propext, Quot.sound]`. Commits `52e5b3e`
(`PinSplit.lean`), `e7179bc` (`PinUp.lean`).

---

## 1. Solo cuentan los pasos con elección (`PinSplit.lean`)

**Demostrado sin hipótesis** (`pin_keeps_of_all`): si todos los nodos vivos de un paso llevan el mismo nodo
de mapa, fijarlo deja el estado válido. Las tablas del estado son un soporte que ya cumple la fijación, y
sobreviven a ella y al review.

Con eso, `PinExtends` se reduce a `PinExtendsChoice`: la hipótesis solo hace falta donde dos nodos vivos
del paso llevan mapas distintos.

## 2. De abajo arriba (medido)

La sonda `pinup` fija los pasos en orden 0, 1, 2… probando en cada uno **todos** los mapas vivos:

| familia | paso | pasos | con un solo mapa vivo | candidatos | candidatos que fallan |
|---|---|---|---|---|---|
| K4 | variable / negación / cláusula | 60 / 60 / 180 | 30 / **60** / **180** | 90 / 60 / 180 | **0** |
| paridad | variable / negación / cláusula | 90 / 90 / 90 | 25 / **90** / **90** | 155 / 90 / 90 | **0** |
| prisma | variable / negación / cláusula | 90 / 90 / 260 | 50 / **90** / **260** | 130 / 90 / 260 | **0** |
| K3,3 | variable / negación / cláusula | 90 / 90 / 260 | 50 / **90** / **260** | 130 / 90 / 260 | **0** |
| Tseitin aleatorio, 8 vértices | variable / negación / cláusula | 120 / 120 / 340 | 70 / **120** / **340** | 170 / 120 / 340 | **0** |

Dos cosas:

* De abajo arriba, **toda la elección está en los pasos de variable**. Al llegar a una negación o a una
  cláusula ya no queda elección.
* En los pasos de variable **ningún valor vivo falla**: no es que exista alguno bueno, es que **todos** lo
  son.

## 3. Lo demostrado (`PinUp.lean`)

**Sin hipótesis — `decided_off_var`**: con los pasos de abajo decididos, un paso de negación, fusión o
cláusula queda decidido.

* **Negación**: el requisito del nodo nombra el valor de su variable (`reqOfCnf_neg`), y sus owners
  cumplen sus requisitos (`ReqFiltered`).
* **Cláusula**: los tres requisitos de la fila nombran los valores de sus tres literales. Con esos valores
  decididos, los tres bits de la fila quedan fijados, y con ellos su índice (1…7).
* **Fusión**: un solo nodo de mapa.

**La hipótesis — `LivePinUp`**:

> Con los pasos por debajo de `2v` decididos y el estado válido, fijar **cualquier valor vivo** de la
> variable `v` lo deja válido.

**Bajo `LivePinUp` sola:**

| teorema | enunciado |
|---|---|
| `complete_up` | fijar de abajo arriba nunca se atasca y termina con todos los pasos decididos |
| `chain_up` | todo estado válido del lector contiene un camino (`chain_of_ids`, v144) |
| `verdict_iff_up` | la máquina tiene un estado final válido ⟺ φ es satisfacible |
| `answer_unsat_up` | a una fórmula insatisfacible responde UNSAT |
| `answer_ne_unknown_up` | nunca responde "no sé": el lector no se atasca y su certificado pasa la comprobación |

## 4. Cómo queda todo

| afirmación | hipótesis |
|---|---|
| toda respuesta (UNSAT, o SAT con certificado) es correcta | **ninguna** |
| un estado válido con un mapa por paso es un camino | **ninguna** |
| negación, fusión y cláusula quedan decididas por los pasos de abajo | **ninguna** |
| la máquina decide; nunca responde "no sé" | **`LivePinUp`** |

La hipótesis habla de un solo estado y un solo paso: *un valor que sobrevive al review, con el prefijo
fijado, nunca es una trampa*. Es la continuación de un trozo de camino ya decidido, lo que hace tu UP.

## 5. Siguiente paso

Atacar `LivePinUp` directamente (en curso).

## 6. Nota técnica

`omega` introduce `Classical.choice` cuando demuestra una conjunción o cuando el contexto tiene
conjunciones negadas o implicaciones aritméticas; `beq_self_eq_true` sobre `Int` también. Hay que
partir las metas y limpiar esas hipótesis antes de llamarlo.
