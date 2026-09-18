# Verificación para el Autor v146: la misma dificultad desde los dos lados — lectura y uniones

Ricardo, soy Claude (Opus 5). Este informe recoge el ataque a `LivePinUp` (la única hipótesis que quedó en
v145) y, tras tu observación sobre UP, el ataque a la distributividad del review sobre la unión.

Rama `spaik`, build de `AbsSat` (212 jobs), sin `sorry`, `[propext, Quot.sound]`. Commits `a979c62`
(`TripleA.lean`) y el de este informe (`JoinSide.lean`).

---

## 1. `LivePinUp` por la vía directa: refutada por medición

Para que fijar un valor vivo `a` mantenga el estado válido basta un **soporte** dentro del estado que ya
lleve la fijación. El candidato natural son **los nodos que poseen a `a`**, con las tablas restringidas a
ellos. `TripleA.lean` demuestra que lo es bajo una condición: la **regla de ternas a través de `a`** (dos
nodos que poseen a `a` y se poseen entre sí tienen en cada paso un nodo común que también posee a `a`; y lo
mismo por padres e hijos). La cobertura sale gratis del review.

La sonda `triplea` dice que esa regla **falla**, ya en la primera variable:

| familia | valores vivos | la regla se cumple | falla |
|---|---|---|---|
| K4 | 27 | 15 | 12 |
| paridad | 45 | 35 | 10 |
| prisma | 39 | 21 | 18 |

El review tiene que quitar más antes de estabilizarse; no hay regla local de tres nodos que lo explique.
Mientras tanto `LivePinUp` sigue sin un solo fallo: `pinup` sobre **240 fórmulas aleatorias** (5–7
variables), 621 recorridos completos, 5.387 candidatos de variable, **0 fallos**.

## 2. Tu observación sobre UP, y dónde está el hueco

Tienes razón: en cada UP el estado es viable, porque antes van el filtrado de requisitos y el review, y la
máquina descarta lo inválido. **Por rama**, eso está demostrado sin hipótesis (`sat_of_oracle_path`).

El hueco son las **uniones**: cuando dos ramas llegan al mismo nodo de mapa, la máquina las une y el
review trabaja sobre la unión. Que la unión sea válida no implica que cada nodo vivo pertenezca a una rama
válida por sí misma. Lo que cierra ese hueco es la **distributividad**: revisar la unión = unir las ramas
revisadas. Con ella, tu argumento por ramas pasa al estado unido y `LivePinUp` sale también. Son la misma
dificultad, vista desde la lectura y desde la construcción.

## 3. El ataque a la distributividad (`JoinSide.lean`)

v140 la redujo a **partir** las tablas de la unión revisada en dos soportes, uno dentro de cada rama,
anclando cada entrada en un nodo común del **paso de arriba** (`PartSplit`), y la sonda `split` midió que
esa partición cumple todas las condiciones en las uniones de la máquina.

**Demostrado sin hipótesis:**

* **`entry_side`** — una entrada de la unión que nombra un nodo **ausente de una rama** viene de las tablas
  de la otra: la unión junta las listas de owners, y los owners de una rama son nodos de esa rama.
* **`part_of_anchor`**, **`cover_of_sideCover`** — en las uniones de la máquina los nodos de arriba de las
  dos ramas son distintos (mismo mapa, padre distinto). Entonces las entradas hacia el ancla vienen solas
  del lado del ancla, y la **mitad de cobertura** de la partición se reduce a un único enunciado:

> **`SideCover`**: cada entrada de la unión revisada tiene un ancla arriba en un lado cuyas tablas llevan
> esa entrada.

**Medido** (sonda `sidecls`, todas las uniones de la ejecución y sus versiones fijadas):

| familia | uniones | nodos de arriba compartidos | entradas | cumplen `SideCover` |
|---|---|---|---|---|
| K4 | 65 | 0 | 56.780 | **56.780** |
| paridad | 474 | 0 | 746.071 | **746.071** |
| prisma | 129 | 0 | 359.180 | **359.180** |

Confirma la separación arriba (0 nodos compartidos) y `SideCover` sin excepción.

## 4. Cómo queda todo

| afirmación | hipótesis |
|---|---|
| toda respuesta (UNSAT, o SAT con certificado) es correcta | **ninguna** |
| la máquina decide; nunca responde "no sé" | `LivePinUp` (lectura) |
| … o, por la construcción | distributividad = `PartSplit` en las uniones |
| cobertura de `PartSplit` | `SideCover` (medido sin excepción) |
| que las dos partes sean soportes | medido (`split`), sin demostrar |

## 5. Siguiente paso

Demostrar `SideCover`. La idea a probar: la rama recién enviada tiene **un único** nodo arriba, que todos
sus nodos poseen; una entrada que solo lleva esa rama tendría que seguir anclada en él tras el review de la
unión. Si eso se sostiene, falta la otra mitad: que cada parte cumpla las condiciones de soporte.
