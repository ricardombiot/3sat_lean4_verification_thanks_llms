# Verificación para el Autor v93: el caso 17 sobre `SatMachinePure` — por qué el hueco de la tabla no llega al final

Ricardo, soy Claude (Opus 5). Me pediste volver al caso 17 de v69, pero esta vez ejecutándolo
directamente sobre la máquina canónica, `SatMachinePure`, y dejar escrito **por qué tu máquina
filtra esos casos y no aparecen al final**. Aquí está, con lo medido llamado medido.

En una frase: **la tabla de owners guarda compatibilidades entre pares que son falsas, pero la
máquina nunca las da por buenas. Cuando una cláusula exige esa combinación, el review la vuelve a
comprobar contra las filas de las cláusulas, y el estado que la contiene muere antes de llegar a la
última línea.**

---

## 1. Sobre qué máquina es esto

Todo lo de este informe corre sobre `run_pure` (`AbsSat/SatMachine/PureSatMachine.lean`). Y hoy
eso ya no es una suposición sobre qué mide qué: `run_pure_eq_driver`
(`AbsSat/SatMachine/PureProofs.lean`, `[propext, Quot.sound]`) demuestra que **la última fila del
timeline de `SatMachinePure` es exactamente `PureDriver.pureRun`**. Una consecuencia útil: toda
campaña anterior que ejecuta `pureAdvance` —la máquina original, sin triángulo— estaba midiendo ya
esta misma máquina.

## 2. El caso 17, ejecutado

Semilla 90210, caso 17: 6 variables, 26 cláusulas, 40 filas de timeline.

| | resultado |
|---|---|
| veredicto de `SatMachinePure` | **SAT** |
| fuerza bruta | SAT |
| estados válidos en toda la ejecución | 145 |
| nodos revisados | 5.088 |
| **nodos zombie** (nodo en ninguna solución de lo visto dentro de su estado) | **0** |

## 3. El hueco sigue ahí

Pares de nodos en pasos distintos que se tienen mutuamente como owners, pero sin ninguna solución
(de las cláusulas vistas, dentro del estado) que pase por los dos:

| | |
|---|---|
| pares co-poseídos revisados | 72.406 |
| **pares sin solución común** | **9** |
| estados que los tienen | **1**, el de clave (17,4) |
| de ellos, hueco también entre **valores del mapa** | 4 |

Son exactamente las 18 entradas simétricas de v69: los nodos `(0,0)`, `(1,1)` y `(2,0)`, que
codifican x0=0 (el último a través de su padre), frente a `(4,1)`, `(5,0)` y `(6,1)`, que codifican
x2=1 (el último, también por su padre). La causa es la de v69: cuando se procesó la cláusula 1,
`x5 ∨ ¬x2 ∨ x0`, x5 aún estaba libre y la fila con x5=1 justificaba el par. La cláusula 4 fija
x5=0 y se lleva esa justificación, pero cada nodo conserva otros owners en el paso 14, así que la
tabla sigue diciendo «compatibles».

**Tu máquina original conserva, por tanto, la inexactitud de tabla que el triángulo corrige.** Lo
que este informe mide es qué hace con ella.

## 4. Por qué no llega al final

El hueco solo sería peligroso si una cláusula posterior exigiera **las dos cosas a la vez**. Así que
lo simulé: en el estado (17,4), para cada par del hueco, fijé los dos valores con `filterAll`, que
es lo que la máquina hace en un paso de cláusula: primero el pin (`filterRequire`) y después el
review.

| par del hueco | tras el pin | tras pin + review | nodos zombie |
|---|---|---|---|
| (0,0)–(4,1) | válido, ningún paso vacío | **inválido**: pasos 13–17 sin owners | — |
| (0,0)–(5,0) | válido, ningún paso vacío | **inválido**: pasos 13–17 sin owners | — |
| (1,1)–(4,1) | válido, ningún paso vacío | **inválido**: pasos 13–17 sin owners | — |
| (1,1)–(5,0) | válido, ningún paso vacío | **inválido**: pasos 13–17 sin owners | — |
| (0,0)–(6,1) | válido, ningún paso vacío | válido; se va el nodo (6,1) | 0 |
| (1,1)–(6,1) | válido, ningún paso vacío | válido; se va el nodo (6,1) | 0 |
| (2,0)–(4,1) | válido, ningún paso vacío | válido; se va el nodo (2,0) | 0 |
| (2,0)–(5,0) | válido, ningún paso vacío | válido; se va el nodo (2,0) | 0 |
| (2,0)–(6,1) | válido, ningún paso vacío | válido; siguen los dos | 0 |

**Control**, en el mismo estado: los **315** pares co-poseídos que **sí** comparten una solución,
fijados de la misma forma, dejan el estado válido en los 315 casos.

Hay dos mecanismos distintos, y los dos son tuyos.

### 4.1 Los cuatro huecos reales: el review encuentra la contradicción

Son los pares entre los pasos 0–1 y 4–5, es decir, entre los valores x0=0 y x2=1 sin intermediario.
Coinciden en número con los 4 huecos entre valores del mapa del §3, y es lo esperable, pero no lo he
comprobado par a par. Tampoco es un argumento cerrado: `ChainSound_filterAll` (`AddNode.lean`)
demuestra que una cadena sonora que respeta los requisitos sobrevive al filtro, pero no he
encontrado un teorema que lleve de `ChainSound` a `isValid`, ni uno que identifique las soluciones
que usa esta medición con cadenas sonoras.

Lo importante es **dónde** muere. **El pin solo no vacía ningún paso**: la tabla, mirada par a par,
no ve ningún problema. Es **el review** quien deja sin owners los cinco pasos de cláusula del 13 al
17. La contradicción vive en la cláusula 1: con x5=0, x0=0 y x2=1, ninguna de sus filas sobrevive.
Y como los nodos de cláusula codifican sus tres literales a la vez, la pérdida se propaga por los
padres e hijos al resto del bloque de cláusulas. No he trazado el orden exacto en que se vacían esos
cinco pasos; lo medido es el resultado.

Y un estado inválido **no se guarda**. En `PureDriver.sendTo` un estado solo se inserta en la línea
siguiente si `isValid` tras el filtrado es verdadero. Por eso **no aparece al final**: no se descarta
un nodo suelto, se descarta el estado entero en el momento del envío.

### 4.2 Los cinco restantes: el filtro trabaja por valor, no por copia

Los otros cinco pares pasan por `(2,0)` o por `(6,1)`, dos nodos que llevan el valor del hueco **a
través de su padre**. El filtro fija **ids del mapa**, no nodos concretos del camino, así que al
fijar el id de `(2,0)` sobreviven también otras copias de ese valor con otros padres, que sí tienen
solución. El review elimina la copia incompatible y deja las demás: estado válido, **0 nodos zombie**
en los cinco casos.

El último, `(2,0)–(6,1)`, merece decirse aparte: **los dos nodos siguen** tras fijarlos, y aun así hay
0 zombis. Cada uno está en alguna solución por su cuenta; lo que no existe es una solución con los
dos. Es la distinción de toda esta línea de trabajo, vista en un solo estado: **el invariante de nodo
aguanta donde el de tabla falla**.

## 5. Lo que esto es, y lo que no

**Medido**, sobre `SatMachinePure`, en un estado de una fórmula:

- la tabla conserva 9 pares falsos;
- ninguno produce un nodo zombie;
- fijar a la vez los dos valores de un hueco real mata el estado por el review, no por el pin;
- fijar un par verdaderamente compatible no mata nunca el estado (315 de 315).

**No demostrado.** Y hay dos límites que conviene dejar escritos:

1. **La simulación fija dos valores sobre un estado intermedio.** Un paso de cláusula real fija tres
   literales mediante `reqOfCnf` en su propio paso. Es la misma operación (`filterAll`), pero no es
   una cláusula insertada de verdad.
2. **El alcance de la propagación es acotado** (v70, §5). Aquí la contradicción está a una cláusula
   de distancia, la 1. En familias como la paridad sobre expansores, la contradicción no se alcanza
   con ningún alcance fijo, y ahí es donde un hueco de tabla sí podría convertirse en zombi. Esto no
   resta nada al resultado; delimita dónde buscar el contraejemplo, si existe.

## 6. Hacia dónde empuja

Lo que la tabla del §4 sugiere como lema, enunciado sobre tus estructuras:

> Si en un estado válido ninguna solución de lo visto combina los valores de dos requisitos, y la
> contradicción está en una cláusula ya vista cuyos otros literales el estado tiene fijados,
> entonces `filterAll` con esos dos requisitos deja el estado inválido.

Es una versión local, con alcance uno, del caso (d) de `FlipCore`. Demostrarla no cierra
`ClauseStepExact`, pero pondría nombre y teorema al mecanismo que hoy solo está medido, y el
parámetro natural para ensancharla —la distancia hasta la cláusula que contiene la contradicción— es
justo el que acota la clase.

---

**Build:** `lake build AbsSat` verde; `PureProofs.lean` sin `sorry`, con `run_pure_eq_driver`,
`completeness_pure`, `soundness_pure` y `run_pure_decides` en `[propext, Quot.sound]`.

## Anexo: cómo reproducirlo

Las mediciones no están en un modo de `cnfmap`; se hicieron con scripts ejecutados desde
`lean_project/` con `lake env lean --run <fichero>.lean`. Usan `nodeZombies`, `prefixOk`, `solPath`
y `solInside` de `AbsSat/GraphMap/SymCampaign.lean`.

- **§2** recorre `(run_pure φ).timeline` y suma `nodeZombies φ alls g` en cada estado válido.
- **§3** cuenta, en cada estado válido, los pares de nodos en pasos distintos con
  `a.owners.contains b.id && b.owners.contains a.id` para los que ninguna solución de `inside`
  contiene los dos.
- **§4** es el script siguiente, tal como se ejecutó. Para la columna «tras el pin», la rama del
  hueco imprimía en su lugar
  `isValid pinned`, `emptySteps pinned`, `isValid full` y `emptySteps full`.

```lean
import AbsSat.GraphMap.SymCampaign
import AbsSat.SatMachine.PureSatMachine
open AbsSat.Utils.Alias AbsSat.Cnf AbsSat.GraphMap.CnfMap AbsSat.GraphMap.CnfMapDiff AbsSat.GraphMap.SymCampaign
open AbsSat.GraphPath.Model AbsSat.GraphPath.Model.GPathM AbsSat.SatMachine.PureSatMachine

def case17 : Option Cnf := Id.run do
  let mut rng := AbsSat.SatMachine.DiffTest.Rng.ofSeed 90210
  let mut base : Option Cnf := none
  for idx in [0:18] do
    let (rng1, nv) := rng.below 3
    let nVars := 4 + nv
    let (rng2, nClauses) :=
      if idx % 3 == 2 then
        let (r, extra) := rng1.below (2 * nVars + 1)
        (r, 4 * nVars + extra)
      else
        let (r, nc) := rng1.below (4 * nVars)
        (r, 1 + nc)
    let (rng3, cnf) := AbsSat.SatMachine.DiffTest.gen_cnf rng2 nVars nClauses
    rng := rng3
    if idx == 17 then
      match AbsSat.Cnf.Dimacs.parse (cnf.splitOn "\n") with
      | .ok φ => base := some φ
      | .error _ => pure ()
  base

def emptySteps (g : GPathM) : List Int :=
  (intRange 0 (g.current_step - 1)).filter (fun k => !hasStepEntry g.gowners k)

def main : IO Unit := do
  let some φ := case17 | IO.println "case 17 not found"
  let alls := (List.range (Nat.pow 2 φ.nVars)).map assignOfNat
  let m := run_pure φ
  let some kv := (m.timeline.flatMap id).find? (fun kv => kv.1.step == 17 && kv.1.index == 4 && isValid kv.2)
    | IO.println "state (17,4) not found"
  let g := kv.2
  let seen := alls.filter (fun a => prefixOk φ a g.current_step)
  let inside := (seen.map (fun a => solPath φ a g.current_step)).filter (solInside g)
  let ns := g.nodes.toArray
  let mut ctrl := 0
  let mut ctrlInvalid := 0
  for i in [0:ns.size] do
    for j in [i+1:ns.size] do
      match ns[i]?, ns[j]? with
      | some a, some b =>
        if a.id.id.step != b.id.id.step && a.owners.contains b.id && b.owners.contains a.id then
          let reqs := [a.id.id, b.id.id]
          let pinned := reqs.foldl filterRequire g
          let full := filterAll g reqs
          if !inside.any (fun p => p.contains a.id && p.contains b.id) then
            if isValid full then
              let hasA := full.nodes.any (fun n => n.id == a.id)
              let hasB := full.nodes.any (fun n => n.id == b.id)
              IO.println s!"GAP ({a.id.id.step},{a.id.id.index})-({b.id.id.step},{b.id.id.index}) stays valid: \
gap node A kept={hasA} B kept={hasB} zombie nodes={nodeZombies φ alls full} parents A={repr a.id.parent_id} B={repr b.id.parent_id}"
          else
            ctrl := ctrl + 1
            if !isValid full then ctrlInvalid := ctrlInvalid + 1
      | _, _ => pure ()
  IO.println s!"control: co-owned pairs WITH a common solution={ctrl}, invalid after pinning both={ctrlInvalid}"
```

Aviso práctico: el pin se aplica solo sobre el estado (17,4). Aplicarlo a todos los pares de todos
los estados de la ejecución (72.406 `filterAll`) es mucho más lento.
