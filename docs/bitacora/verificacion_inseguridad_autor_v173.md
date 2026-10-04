# Verificación para el Autor v173: el veredicto en una frase, el testigo por estado, y por qué todo desemboca en la ventana del identificador

Ricardo, soy Claude (Opus 5). Este informe recoge un commit y **dos ideas tuyas**, y explica con cuidado
dónde aterriza cada una. La parte demostrada es corta; la parte explorada es la que importa hoy. Rama
`spaik`, módulo `ImprovesCima.lean`. Build de `AbsSat` (232 jobs), sin `sorry`, axiomas
`[propext, Quot.sound]`.

## 0. Resumen

* **Lo que queda del veredicto cabe en seis líneas de Lean**: `PinnedUnionInhabited` — *toda unión por
  clave que siga viva tras fijar contiene una cadena*. De ahí sale `sat_of_pinnedUnionInhabited`, y nada
  más hace falta.
* Las otras dos mitades **salieron gratis**: que la cadena viva en un lado (porque una cadena de un
  estado de la máquina es un camino genuino, y un envío contiene los caminos genuinos de su fuente) y
  que respete las fijaciones (porque fijar deja en ese paso solo la fijación).
* **Tu idea del testigo por estado** mejora el marco: quita el problema de la reparación. Pero el muro
  no desaparece — **se muda**: si se define "vivo" como "se puede extraer testigo", se rompe la
  conservación, porque el lector codicioso puede atascarse en un estado que sí tiene camino.
* **Tu intuición sobre el review agresivo es cierta para una ronda y está demostrada**; se rompe en el
  trío, y el sitio exacto está escrito en `Descent.extend_of_common_owner`.
* Y las dos exploraciones —la tuya por el lector, la mía por la anchura— **desembocan en el mismo
  sitio**: la ventana de historia del identificador.

## 1. El veredicto, en una frase

```lean
def PinnedUnionInhabited (L : PureLine) : Prop :=
  ∀ p J, (p, J) ∈ pureAdvanceW φ L → ∀ Q,
    isValid (filterAllAgg J Q) = true →
    ∃ sel, ChainSound (filterAllAgg J Q) sel
```

`sat_of_pinnedUnionInhabited`: de eso sale el veredicto SAT de `ImprovesCima`. Toda la maquinaria
—familias, cimas, conos, soportes, lados, restricciones, el descenso— se ha ido consumiendo.

**Las dos mitades que no hizo falta demostrar:**

* *Que la cadena viva en un lado.* Una cadena de un estado de la máquina **es un camino genuino**
  (`genuine_of_chain`), y un envío contiene todo camino genuino que pasa por su fuente
  (`send_complete`). El lado no se elige ni se busca: la genuinidad lo pone.
* *Que respete las fijaciones.* Los nodos de una cadena son dueños globales, y fijar deja en ese paso
  solo la fijación (`filterAllAgg_cleans`).

## 2. Tu idea: extraer un testigo en cada estado

> *"¿Y si tras cada estado ejecutáramos el algoritmo de lectura y nos guardáramos una cadena contenida
> en el conjunto?"*

La idea es buena y mejora la versión que yo había esbozado: **recalcular en cada estado elimina el
problema de la reparación**, que era lo feo de arrastrar un solo testigo.

Lo que el testigo sobrevive está casi todo demostrado ya:

| operación | ¿conserva el testigo? |
|---|---|
| semilla | trivial |
| **UP** (`addNode`) | sí — `ChainSound_addNode` |
| **unión** | sí — `ChainSound_join_left/right` |
| **revisión agresiva** | sí — `ChainSound_reviewAgg` |
| **fijación** | sí **si la cadena la cumple** — `ChainSound_filterRequire` |

Y muere en un sitio muy concreto: en un paso de literal la cadena tiene un valor, así que **siempre hay
un hijo cuyos requisitos cumple** y pasa gratis; en una **fila de cláusula** sobrevive si y solo si la
asignación parcial satisface esa cláusula. El testigo muere exactamente cuando debe.

## 3. Pero el muro se muda, no desaparece

Dijiste: *"si no hay conjunto válido no se puede construir el testigo, entonces no hay estado"*. Ahí hay
un salto, y se ve en la definición, que es de una línea:

```lean
def isValid (g : GPathM) : Bool :=
  (intRange 0 (g.current_step - 1)).all (fun k => hasStepEntry g.gowners k)
```

**Mira cada paso por separado.** Dice que en el paso 0 hay algún dueño vivo, en el 1 hay alguno, en el 2
hay alguno. No dice nada de si se pueden **elegir a la vez de forma coherente**.

Y si lo hiciéramos definición —"vivo := se puede extraer testigo"— el veredicto saldría gratis, pero se
rompería la otra mitad: el lector codicioso puede atascarse en un estado que **sí** contiene un camino
real, y declararlo muerto sería **perder una solución verdadera**. La conservación, que ya está
demostrada, dejaría de valer.

El intercambio, escrito:

| extractor | no falla si hay cadena | polinómico |
|---|---|---|
| codicioso (el lector) | **?** | sí |
| con retroceso | sí | **no** |

La máquina necesita las dos. Tener las dos es lo abierto. La dificultad se puede mover del veredicto a
la conservación, pero no hacerla desaparecer redefiniendo "vivo".

**Lo que sí queda de tu idea, y no es poco:** la pregunta deja de ser *"¿existe una cadena?"* y pasa a
ser **"¿falla alguna vez el lector codicioso en los estados que esta máquina construye?"** — una
pregunta sobre un algoritmo concreto en unos estados concretos, y **medible**.

## 4. Tu intuición sobre el review agresivo

> *"No es posible que ante un conjunto bien construido falle el lector, porque el review agresivo
> asegura en cada paso que todos los nodos del siguiente paso al menos tienen un camino."*

**La parte cierta, y está demostrada.** El review deja dos garantías:

* **`cov`** — todo nodo vivo tiene compañero en **cada** paso;
* **`agg`** — todo par relacionado tiene un dueño **común** en cada paso.

Así que el lector nunca se queda sin candidatos, y con **dos** elegidos siempre hay con qué seguir
(`Descent.extend_anchor`, `extend_pair`).

**Dónde se rompe, con la línea exacta.** El enunciado de la extensión del descenso dice, literalmente:

```lean
(hown : ∀ k, lo ≤ k → k < g.current_step → c ∈ ownersOf g (sel k))
```

El nodo que baja debe ser dueño de **todos** los ya elegidos. El review lo da para uno y para dos. Para
tres, no.

**Tu intuición en su versión fuerte —fijar y revisar— llega más lejos.** Al fijar el paso `k` al valor
`v`, el estado se estrecha a la rebanada de `v`, y todo lo que sobrevive es compatible con `v` por
construcción:

* *primera ronda*: la rebanada sigue viva, **y por tu razón exacta** — `cov` dice que `v` tiene
  compañero en cada paso, así que ningún paso se vacía;
* *la revisión dentro de la rebanada*: para un par `(x,y)` necesita un dueño común **que también esté en
  la rebanada**, es decir dueño común de `x`, `y` **y** `v`. Tres.

Eso tiene nombre aquí desde v122: **`SpcStable`**. Tu camino desemboca en la primerísima forma del muro.

**Un dato tuyo que conviene tener presente.** No es un problema abstracto: en tu máquina la posesión
**no es transitiva**, medido en v132 con **52.720 contraejemplos de 380.746** (y 3.432 de 45.615 en su
forma adyacente). Bajar por los padres siempre se puede; el camino que sale no es automáticamente
coherente. De ahí la lectura que me parece la correcta:

> El lector no acierta porque valga cualquier camino. Acierta porque **existe uno bueno y el codicioso
> lo encuentra**. Por qué lo encuentra es lo abierto.

Y tus 1.146.914 bajadas sin un solo fallo dicen que lo encuentra siempre; todavía no dicen por qué.

## 5. La convergencia

Me hice la pregunta al revés: *¿qué habría que añadirle al review para que tu intuición fuese teorema?*
La respuesta es precisa: **que vea tríos, no pares**.

Y hacer que una revisión de pares vea tríos es exactamente **dar al identificador un nivel más de
historia**: el nodo pasa de *(nodo, padre)* a *(nodo, padre, abuelo)*. Entonces "dos nodos" en el mundo
nuevo son "tres" en el viejo, y la misma revisión agresiva —sin tocarla— pasa a dar consistencia de
tríos.

Es el truco clásico de codificar tuplas como variables, y aquí **sale barato porque tu máquina ya está
construida sobre identificadores con historia**: ya guarda un nivel, y es justo eso lo que hace que el
review dé pares y no menos. Nadie ha tocado ese mando.

* Coste: grado de entrada elevado a `c−1` estados por nodo del mapa. **Polinómico para `c` fijo.**
* No lo refuta el aviso de v130 ("identificadores de un solo padre harían del ID un camino,
  exponencial"): eso era para historia **ilimitada**. Una ventana acotada no es un camino.
* Lo que daría: **consistencia fuerte de orden `c+1`**, y con ella —por el teorema clásico de anchura—
  completitud demostrable para las fórmulas cuya anchura inducida bajo el orden del mapa sea menor que
  `c`. Es un resultado de **clase acotada**, con matemática conocida detrás, no un problema abierto.

Las dos exploraciones —la tuya por el lector, la mía por la anchura— desembocan en el mismo mando. Eso
me da bastante confianza en que es el correcto.

## 6. Lo que propongo

1. **Demostrar la mitad de tu intuición que sale**: fijar a un nodo vivo no vacía ningún paso. Trabajo
   seguro, y deja el resto aislado en una sola frase (`SpcStable` dicho limpio) con todo lo demás
   demostrado alrededor.
2. **Medir la ventana**: el grado de entrada real de tu mapa y la anchura inducida de unas familias de
   fórmulas. Eso dice de golpe cuánto cuesta subir a `c = 2` y qué clase quedaría cubierta.
3. Y, si los números acompañan, **subir la ventana**: un cambio de diseño acotado en tu máquina que
   convierte tu intuición en teorema hasta el orden que alcance.

## 7. Descartado por el camino

Para que no parezcan puertas abiertas:

* **Arrastrar un solo testigo**: muere en las filas de cláusula y elegir otro *es* el problema. Tu
  versión —recalcular por estado— lo evita, pero mueve la dificultad a la conservación.
* **Diagramas de decisión**: refutado en v137; los estados con la misma clave casi nunca comparten
  futuro, así que no comprimen.
* **Quitar los nodos que no estén en ninguna cadena**: calcular eso es el problema de vacuidad por nodo.
* **Transitividad de la posesión**, en cualquiera de sus formas: refutada por medición en v132.

## 8. Commits

`b378647` (`PinnedUnionInhabited`, `rulePreserves_of_chain`, `sat_of_pinnedUnionInhabited`).
