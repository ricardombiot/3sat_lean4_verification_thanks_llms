# Verificación para el Autor v134: qué es exactamente `CommonOwner`

Ricardo, soy Claude (Opus 5). Me preguntas si `CommonOwner` es una propiedad que la máquina **debe
cumplir** para responder correctamente y si, en caso de fallar, el problema sería de la
**implementación** y no de la teoría que sostiene que tal máquina puede existir.

La respuesta corta: **sí, con un matiz importante y una corrección**. El matiz es que un fallo no
sería de la implementación en el sentido de "un bug que se arregla", sino de la **abstracción** —y ese
coste es medible—. La corrección es que hay **dos** afirmaciones distintas escondidas en "responder
correctamente", y `CommonOwner` solo hace falta para una de ellas. La otra está demostrada sin
hipótesis. Ese punto es el más importante de este informe y va primero.

Rama `spaik`, build de `AbsSat` (191 jobs), sin `sorry`, `[propext, Quot.sound]`.

---

## 1. Lo primero: hay dos afirmaciones, y solo una necesita la hipótesis

**(A) "Cuando la máquina responde SAT *y entrega el camino*, la respuesta es correcta."**
**Demostrado, sin hipótesis.**

> `NoDeadEndVerdict.sat_of_denotS` — si el estado del lector **denota** un camino, φ es satisfacible.

El camino se decodifica a una asignación (`CnfChain.sat_of_reqSatisfying`) y esa asignación satisface
φ. Es decir: **toda respuesta SAT acompañada de su camino se certifica a sí misma**, y además el
certificado es verificable en tiempo lineal por cualquiera, fuera de la máquina y fuera de Lean. Aquí
`CommonOwner` no aparece.

**(B) "Cuando el estado final es válido, φ es satisfacible" —concluir SAT desde la validez, sin
exhibir el camino.** **Necesita `CommonOwner`.**

> `NoDeadEndVerdict.sat_of_commonOwner`

Esta es la afirmación que convierte la validez del estado en un veredicto. Y es la que necesita que el
lector **pueda siempre leer** un camino cuando el estado es válido, o sea que no se quede atascado.

**Consecuencia práctica, que responde a medias tu pregunta:** si `CommonOwner` fallara en una
instancia, las respuestas que la máquina **emite con camino** siguen siendo correctas; lo que se
perdería es el derecho a decir "es válido, por tanto SAT" sin más. La máquina seguiría siendo útil y
fiable en el uso normal —responde y entrega certificado—, pero dejaría de ser un decisor demostrado en
ese sentido fuerte.

Y al revés: el sentido UNSAT (`pureRunW_ne_nil`) está demostrado **sin hipótesis**. Un "no hay camino"
es de fiar siempre.

## 2. Qué dice `CommonOwner`, con precisión

```lean
def CommonOwner (g : GPathM) : Prop :=
  ∀ (sel : Int → PathNodeId) (lo : Int), 0 < lo → lo ≤ g.current_step - 1 → SoundFrom g sel lo →
    ∃ c nc, g.node? c = some nc ∧ c.id.step = lo - 1 ∧
      ∀ k, lo ≤ k → k < g.current_step → c ∈ ownersOf g (sel k)
```

En palabras: toma un estado `g` de la máquina y una **cadena parcial** suya —una elección de un nodo
por paso desde el paso alto hasta un paso `lo`, con enlaces de padre e hijo entre consecutivos y
pertenencia mutua entre todos—. Entonces existe un nodo `c` en el paso `lo - 1` que **todos** los picks
de la cadena tienen en su tabla de owners.

Tres cosas que conviene notar:

- Es una propiedad **de un estado**, no de la fórmula ni de la ejecución. Se comprueba mirando las
  tablas de ese estado.
- Es **decidible y finita**: para un estado concreto se puede verificar exhaustivamente, y eso es
  exactamente lo que hace la sonda `helly dead`.
- No pide nada de fijaciones, uniones ni rebanadas. Un estado, un paso.

## 3. Por qué el descenso pide exactamente eso, y nada más

Está demostrado que `CommonOwner` es **todo** lo que falta, en este sentido literal:

> `Descent.extend_of_common_owner` — si los picks tienen un owner común en el paso inferior, ese owner
> **es** un padre del pick más bajo y **todas** las demás condiciones de cadena se siguen de los
> invariantes de la máquina.

El desglose, porque es la parte que más me sorprendió al demostrarla. De las siete condiciones que
define una cadena parcial, el owner común da:

| condición | de dónde sale |
|---|---|
| es un nodo del paso correcto | del owner común, por `GN` |
| enlace de **padre** | `AdjacentOwners`: los owners del paso inferior **son** los padres |
| enlace de **hijo** | `AdjacentOwners`: los owners del paso superior **son** los hijos |
| pertenencia mutua con los picks | el owner común en un sentido; la **simetría** de tu barrido en el otro |
| owner global | `ownGow`: un owner en rango es owner global |
| auto-pertenencia | `self` |
| forma de raíz | `NotRoot` y `RootAtZero` |

Es decir: **el único grado de libertad del descenso es la existencia del owner común**. Todo lo demás
lo fija la estructura que la máquina ya mantiene. Por eso el enunciado no se puede debilitar más sin
dejar de servir.

## 4. Lo que la máquina ya garantiza, y el hueco exacto

Tu barrido agresivo con filtro simétrico (v121) demuestra esto de todo estado revisado:

> `AggFixpoint.aggOk_reviewAgg` — las tablas son **simétricas** y **dos owners cualesquiera comparten
> una entrada en cada paso**.

O sea: `CommonOwner` **par a par** está demostrado. Lo que falta es pasar de los pares al conjunto
entero de picks. Y los picks no son un conjunto cualquiera: son una **clique** de la relación de
compatibilidad (todos se poseen mutuamente) enlazada por padres e hijos.

En el vocabulario de propagación de restricciones, que es donde este hueco tiene nombre propio:

- la máquina mantiene **2-consistencia** (consistencia de arcos, reforzada: pares compatibles con
  testigo en cada paso);
- el descenso necesita **k-consistencia** (un testigo común para el conjunto entero).

Y el resultado clásico es que **la 2-consistencia no implica la k-consistencia** salvo que la red de
restricciones tenga estructura (anchura inducida 1, es decir, árbol). Aquí la red **no** es un árbol:
los requisitos de cláusula conectan pasos lejanos. Por eso no es un descuido de la prueba: es el punto
donde una propiedad global tiene que venir de la construcción, no de las reglas locales.

## 5. Cinco intentos de reducirla a algo local, y por qué fallan

Cada una de estas reglas habría cerrado `CommonOwner` sin k-consistencia. Las cinco están **refutadas
por medida** (v130, v132):

| regla | qué habría dado | fallos medidos |
|---|---|---|
| transitividad de la pertenencia | cualquier padre extiende | 52.720 / 380.746 |
| transitividad restringida a padres | cualquier padre extiende | 3.432 / 45.615 |
| el pick vecino decide el padre | elección local del testigo | 220 / 6.767 |
| la rebanada de un nodo es una clique | el ancla como testigo común | 182.860 / 1.254.448 |
| candidatos anidados al subir la cadena | la intersección sería la del ancla | 175.024 / 9.073.621 |

La lectura conjunta: **el owner común existe siempre, pero la información que lo elige no está en
ningún patrón local ni monótono de las tablas**. Está repartida por toda la cadena —un contraejemplo
de v132 muestra un candidato aceptado por el pick de un paso más arriba y rechazado por el de **siete**
pasos más arriba—.

## 6. A qué es equivalente

`CommonOwner` no es un tecnicismo aislado: es la forma mínima de una propiedad que ya conocemos de
trece informes.

- **Es equivalente a la exactitud de las tablas**: que la tabla de owners de un nodo sea exactamente el
  conjunto de elecciones que están en **algún camino** que pasa por él, y no un superconjunto. Con
  exactitud, el owner común existe porque hay un camino; sin ella, la tabla puede afirmar
  compatibilidades que ningún camino realiza.
- **Es la forma mínima** de las siete reducciones ya demostradas: fijaciones exactas (v119),
  `SpcStable` (v122), `PairChain` (v123), sin préstamos entre ramas (v127), validez hereditaria (v128),
  `JoinsSplit` (v128). Todas son **suficientes** y todas son **más fuertes** de lo necesario.
- **Es lo que las sondas miden desde v119**. La tabla de evidencia, toda con 0 excepciones:

| hecho medido | volumen |
|---|---|
| el descenso nunca se atasca (espacio de cadenas **entero**) | 5 familias Tseitin, ~3,4 M extensiones |
| las cadenas de una unión nunca se mezclan | 6 familias, 5.679 uniones, 1.027.901 cadenas |
| las fijaciones son exactas | 19,2 M entradas |
| fijar = construir la rama | 1.725 fijaciones |
| `PairChain`: ningún par de owners sin cadena | todas las líneas y recorridos |

## 7. Tu pregunta: ¿implementación o teoría?

Separo tres cosas que se confunden con facilidad.

**(a) ¿Existe una máquina correcta?** Sí, trivialmente: la fuerza bruta. La existencia de *una* máquina
correcta no está en juego, así que un fallo de `CommonOwner` no refutaría nada de eso.

**(b) ¿Es un fallo de la implementación?** En parte sí: `CommonOwner` es una propiedad de los estados
que **esta** máquina construye, luego un fallo sería un fallo de **este diseño en esa instancia**, no
de la teoría. Y sería reparable con un review más fuerte, o con más información por entrada. Pero aquí
está el matiz que no quiero que se pierda: **la reparación no es gratis**. Las cinco reglas refutadas
dicen que la información que falta **no está** en las tablas tal como son. Para tenerla hay que
guardar la **procedencia** de cada entrada (v129 §5) o separar las historias en el ID (v130 §3), y las
dos cosas cuestan espacio. Así que un fallo no sería "un bug", sería **una medida del precio de la
abstracción**: el mecanismo que evita la explosión espacial es el mismo que borra la información que
haría demostrable `CommonOwner`.

**(c) ¿Y la teoría que sostiene que esta máquina puede existir?** Lo que un contraejemplo tocaría es
esa afirmación concreta —que **esta** forma de abstraer (tablas de compatibilidad por pares, con
uniones que mezclan historias y un review que solo poda) basta para decidir desde la validez—. No
tocaría nada más. Y hasta donde he podido medir, no hay contraejemplo: más de tres millones de
extensiones del descenso y más de un millón de cadenas de uniones, sin una excepción.

## 8. Cómo se falsaría, si alguien quiere intentarlo

Un contraejemplo es un objeto concreto y pequeño de describir:

> un estado válido y revisado de la máquina, una cadena parcial suya, y la comprobación de que **ningún**
> nodo del paso inmediatamente inferior está en las tablas de owners de todos sus picks.

La sonda `helly dead` busca exactamente eso, recorriendo el espacio **entero** de cadenas parciales de
cada estado (no una muestra) y contando `DEAD_ENDS`. Cualquier valor distinto de 0 es un contraejemplo.
Dónde buscaría yo, por orden: fórmulas de paridad grandes (`par32`), 3-SAT aleatorio en el umbral
(ratio ≈ 4,26), palomar, y familias con muchas uniones por paso —que es donde las historias se mezclan
más—.

## 9. Lo que `CommonOwner` no es

- **No es una afirmación de coste.** No dice nada del tiempo ni del espacio de la máquina, ni de clases
  de complejidad. Es corrección condicional del veredicto de esta máquina.
- **No es necesaria para confiar en una respuesta concreta.** Una respuesta SAT con su camino está
  certificada sin ella (§1).
- **No es una hipótesis sobre φ.** Es una propiedad de los estados que la máquina construye, y por eso
  se puede comprobar instancia a instancia.

## 10. Resumen en cinco líneas

1. Sentido UNSAT: demostrado **sin hipótesis**.
2. Respuesta SAT **con camino**: correcta y autocertificada, demostrado **sin hipótesis**.
3. Concluir SAT **desde la validez**: demostrado **bajo `CommonOwner`**.
4. `CommonOwner`: los picks de una cadena parcial tienen un owner común un paso más abajo. Un estado,
   un paso. Equivalente a la exactitud de las tablas. Medido sin excepción; cinco reducciones locales
   refutadas.
5. Un fallo suyo señalaría el **precio de la abstracción**, no un bug ni un límite de la teoría general.
