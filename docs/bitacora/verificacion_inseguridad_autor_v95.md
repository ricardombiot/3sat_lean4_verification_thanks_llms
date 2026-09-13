# Verificación para el Autor v95: qué hace tu máquina por encima de la propagación — ramas por fila, y la tabla de owners

Ricardo, soy Claude (Opus 5). v94 dejó abierta una pregunta: si el review contiene la propagación
unitaria, ¿hace algo más? Me pediste explorarla con calma. Salen dos cosas, y las dos están
demostradas:

1. **El conductor ramifica por filas de cláusula.** Cada estado de la línea lleva fijados los literales
   de su fila clave, y una fila que contradice esa clave nunca se extiende.
2. **La tabla de owners guarda qué valores conviven.** Un valor sobrevive a un filtro solo si convive
   con todos los valores fijados; la propagación unitaria, que mira cada variable por separado, no
   puede verlo.

Y por el camino tuve que **retirar una conclusión mía**: la dejo escrita porque es lo que da sentido a
lo demás.

---

## 1. La pregunta, y una familia construida para ella

La hipótesis era que tu máquina razona sobre **filas de cláusula** y no solo sobre variables. La prueba
natural son cuatro cláusulas que la propagación no refuta pero la consistencia entre cláusulas sí:

```
a ∨ b ∨ c      a ∨ ¬b ∨ c      ¬a ∨ b ∨ c      ¬a ∨ ¬b ∨ c
```

Con `c` falso ninguna combinación de `a` y `b` sirve; pero cada cláusula conserva dos literales libres,
así que la propagación nunca tiene nada que forzar.

Las inserté en fórmulas del generador de las campañas (semillas 1001, 7777 y 31337; 70 fórmulas, `a`,
`b`, `c` y la polaridad de `c` al azar) y miré los 306 estados válidos de `SatMachinePure` posteriores
a las cuatro cláusulas:

| | estados |
|---|---|
| el valor falso de `c` sigue presente | **0** |
| ha desaparecido, y la propagación desde los dominios del estado lo explica | 247 |
| ha desaparecido, y la propagación **no** lo explica | 59 |

## 2. Lo que dije, y por qué no era así

Te dije que en esos 59 la máquina hacía algo más que la propagación. Seguí uno paso a paso (semilla
1001, `a=2`, `b=0`, `c=3`, cinco cláusulas) y **no era así**:

- en la línea 12 del conductor solo queda un estado con `c` falso, el (12,2);
- sus siete envíos salen inválidos, y en los siete **el propio pin ya vacía un paso**, antes del review:
  la fila destino exige un valor que el estado ya no tiene;
- la propagación, desde los dominios de ese estado, ve el conflicto en todos ellos.

La medición de los 59 se hizo sobre **estados finales**, que son uniones de estados de filas distintas:
sus dominios juntan valores de ramas diferentes y ocultan que cada rama, por separado, ya estaba
refutada. La fuerza no estaba en el review: estaba en que **el conductor mantiene un estado por fila
clave**.

Lo comprobé después en los 59, recorriendo **todos** los envíos del bloque de cláusulas de esas 59
fórmulas y comparando, en cada uno, el punto fijo de la propagación sobre el estado con los pins
aplicados con lo que deja `filterAll`:

| | |
|---|---|
| envíos revisados | 24.936 |
| envíos inválidos **sin** conflicto de propagación | **0** |
| envíos válidos que pierden `c` falso | 899 |
| … de ellos, la propagación ya lo excluía | **899** |

Confirmado para los 59: nunca fue el review quien quitó `c` falso.

## 3. Primer teorema: el conductor ramifica por filas clave

`AbsSat/GraphPath/Model/KeyBranching.lean`, todo en `[propext, Quot.sound]`:

```lean
def KeyPure (φ : Cnf) (kv : NodeId × GPathM) : Prop :=
  ∀ q ∈ kv.2.gowners, ∀ r ∈ reqOfCnf φ kv.1, q.id.step = r.step → q.id = r

theorem pureAdvance_keyPure (φ) (hwf : WF φ) (line) :
    ∀ e ∈ pureAdvance φ line, KeyPure φ e

theorem pureAdvance_drops_key_conflict (φ) (hwf) (k) (line) (hl : LineOk φ k line)
    (hk : litBlock φ ≤ k) (kv) (hkv : kv ∈ pureAdvance φ line)
    (d) (v) (hv : v < φ.nVars) (b) (hb : b = 0 ∨ b = 1)
    (hkey : ReqValue φ kv.1 v b) (hdest : ReqValue φ d v (1 - b)) (next) :
    sendTo φ kv.2 next d = next
```

*Cada estado que el conductor guarda lleva fijados los literales de su fila clave* —el envío los fija y
las uniones solo mezclan estados con la misma clave—, *y si la fila destino exige para una variable el
valor contrario, ese envío se descarta.* La prueba sale de v94: la clave refuta un valor, el pin del
destino el otro, y `sendTo_of_refuted` cierra.

Es exactamente lo que se vio en la traza: el envío de (12,2) a (13,4) muere porque la clave exige x2=1
(nodo `(5,0)`) y el destino x2=0 (nodo `(5,1)`).

## 4. Pero sí hay algo más: 8 valores

La misma comprobación general —*cualquier* valor que la propagación todavía permite y que el review
quita dejando el estado válido— encontró **8**, todos en la semilla 31337. Es la primera vez que el
review hace visiblemente más que la propagación.

Los clasifiqué reproduciendo el review etapa a etapa (limpieza con owners globales, pasada de padres,
pasada de hijos, en bucle) y comprobando que la reproducción coincide con `review`:

| | valores |
|---|---|
| mueren en la **primera limpieza** (`cleanInvalid`) | **8 / 8** |
| el paso que queda sin owner es un **paso fijado** por los pins | **8 / 8** |
| intervienen las pasadas de padres o de hijos | 0 |

Dos detalles honestos: son en realidad **4 casos distintos**, porque salen de dos variantes de la misma
fórmula base con idéntico comportamiento de la máquina; y no todos son el enlace con el padre.

- **x4=0**, nodo `(8,0)`: su único owner en el paso 7 es su padre `(7,0)`, que significa x3=1. El pin
  x3=0 lo quita de los owners globales, y en la limpieza el nodo se queda sin owner en el paso 7.
- **x5=1**, nodo `(10,1)`, tres pasos más arriba: sus owners en el paso 7 tampoco incluían el valor
  fijado. No es el padre: es la tabla recordando, a distancia, con qué convive ese valor en el estado.

## 5. Segundo teorema: lo que sobrevive convivía con los pins

`AbsSat/GraphPath/Model/PinSupport.lean`, `[propext, Quot.sound]`:

```lean
theorem pinned_support (g) (hgn : GownersNodes.GN g) (reqs)
    (hv : isValid (filterAll g reqs) = true) (r : NodeId)
    (hp : Present (filterAll g reqs) r) :
    ∃ n ∈ g.nodes, n.id.id = r ∧
      ∀ req ∈ reqs, 0 ≤ req.step → req.step < g.current_step → ∃ q ∈ n.owners, q.id = req

theorem removed_unless_supported (g) (hgn) (reqs) (r)
    (hns : ∀ n ∈ g.nodes, n.id.id = r →
      ∃ req ∈ reqs, 0 ≤ req.step ∧ req.step < g.current_step ∧ ∀ q ∈ n.owners, q.id ≠ req) :
    isValid (filterAll g reqs) = false ∨ ¬ Present (filterAll g reqs) r
```

*Si un valor sobrevive a un filtro válido, algún nodo que lo lleva ya tenía como owner, en cada paso
fijado, exactamente el valor fijado. Dicho al revés: el filtro elimina todo valor que en ese estado
nunca aparece junto a lo fijado.* La prueba es corta porque todas las piezas ya estaban: el nodo
superviviente es válido, tiene owner en cada paso, ese owner es owner global, y el pin solo dejó el id
fijado. Solo pide `GN`, que tienen todos los estados alcanzables.

Los 8 valores del §4 cumplen la hipótesis del segundo teorema: sus owners en el paso 7 no incluían el
valor fijado.

## 6. Lo que queda dicho

| nivel | qué hace | estado |
|---|---|---|
| propagación unitaria | un conflicto de propagación invalida el filtro | ✅ v94 |
| conductor por filas clave | una fila que contradice la clave no se extiende | ✅ `KeyBranching.lean` |
| tabla de owners frente a los pins | un valor que no convive con los pins se elimina | ✅ `PinSupport.lean` |
| compatibilidad completa por pares | no la tiene: el caso 17 conserva 9 pares falsos | medido (v93) |
| `ClauseStepExact` | abierto, sin cambios |

**Lo que no es:**

- El segundo teorema habla de un valor frente a los pins, no de parejas arbitrarias de valores del
  estado. La tabla no es exacta a nivel de pares (v69, v93), y este resultado no lo contradice.
- La familia de cuatro cláusulas es una sola construcción, y los 8 valores son 4 casos. Lo demostrado
  no depende de eso; lo medido, sí.
- Nada de esto mueve el muro de v70.

Build: `lake build AbsSat` verde, 0 `sorry`; los teoremas nuevos fijados con `#guard_msgs` en
`[propext, Quot.sound]`.

## Anexo: cómo se midió

Todo con scripts desde `lean_project/` (`lake env lean --run <fichero>.lean`) sobre `run_pure` y el
conductor (`pureInit`, `pureAdvance`), con el generador de las campañas (`DiffTest.gen_cnf`,
`Rng.ofSeed`); no están en un modo de `cnfmap`.

- **Familia**: por semilla, 8 fórmulas base con `4 + Rng.below 3` variables y `1 + Rng.below (2·n)`
  cláusulas; por cada una, 6 variantes con `a`, `b`, `c` distintos y polaridad de `c` al azar, añadiendo
  las cuatro cláusulas al final.
- **«La propagación no lo explica»** (§1): en un estado válido posterior a las cuatro cláusulas sin el
  valor falso de `c`, se toman los dominios del estado (un valor está permitido si sus nodos en el paso
  de la variable y en el de su negación son owners globales), se fuerza `c` falso y se propaga sobre las
  cláusulas vistas; si no hay conflicto, cuenta.
- **Comprobación de envíos** (§2 y §4): para cada envío del bloque de cláusulas, punto fijo de la
  propagación sobre el estado con los pins aplicados; se cuentan los envíos inválidos sin conflicto, y los
  valores que ese punto fijo permite pero que faltan en los owners globales de `filterAll`.
- **Clasificación** (§4): reproducción de `reviewFuel` etapa a etapa; cuando desaparece un nodo con el
  valor, se registran los pasos donde se queda sin owners tras la intersección de esa etapa y si alguno es
  un paso fijado.
