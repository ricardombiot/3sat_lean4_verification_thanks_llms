# Verificación para el Autor v42: `SAbove` demostrado — y con él, el enhebrado completo

Ricardo, soy Claude (Opus 5). v41 dejó nombrado el invariante que faltaba. Está demostrado, y con él el teorema de enhebrado ya no es medio: **todo nodo por encima del paso 0 está en un camino completo, del paso 0 hasta la cima, cuyos nodos lo poseen todos.**

---

## 1. `SAbove`

```lean
def SAbove (h : GPathM) : Prop :=
  ∀ n ∈ h.nodes, ∀ s ∈ n.sons, s.id.step = n.id.id.step + 1

theorem SAbove_reachable (g : GPathM) (h : Reachable reqOf g) : SAbove g
```

Cierre `[propext, Quot.sound]`. `AbsSat/GraphPath/Model/Sons.lean`.

`Parents.PBelow` —todo padre un paso por debajo— sale gratis de `Pruned`, porque `Pruned` lleva una cláusula `parents ⊆`. Su espejo **no**, y ahí estaba el trabajo.

Pero salió más barato que `SMP`, y por una razón que merece decirse: **`SAbove` es local** —relaciona un nodo con sus propios hijos—, así que todas las operaciones de poda quedan cubiertas por un solo lema:

```lean
def SonsSub (g g' : GPathM) : Prop :=
  ∀ n' ∈ g'.nodes, ∃ n ∈ g.nodes, n'.id = n.id ∧ ∀ s ∈ n'.sons, s ∈ n.sons

theorem SAbove_of_SonsSub (hs : SonsSub g g') (h : SAbove g) : SAbove g'
```

> Los ids no cambian y los hijos solo encogen. **Ésa es la cláusula que le falta a `Pruned`.**

`updateAt`, `removeNode`, `unlinkIncompatible` y `filterRequire` son todas `SonsSub`, y el resto de la review se compone. La única operación con algo que decir es `addNode`, y lo que dice **es** el contenido del invariante: la guarda de `upSons` reparte el nodo nuevo exactamente a la línea de un paso por debajo.

## 2. El enhebrado, ahora completo

```lean
theorem threaded (g) (ctx : TCtx g) (a) (n) (hn : g.node? a = some n) (hself : a ∈ n.owners)
    (h1 : 1 ≤ a.id.step) (hahi : a.id.step < g.current_step) :
    ∃ sel, IsChain g sel ∧ ∀ i, 0 ≤ i → i < g.current_step → a ∈ ownersOf g (sel i)
```

Cierre `[propext, Quot.sound]`, ensamblado para los estados de la máquina en `threaded_filterAll`.

La construcción tiene dos mitades y usan cosas distintas:

- **Subir** (`climb`): `coherent_sons` dice que si `d` posee `a`, algún hijo de `d` posee `a`; `SAbove` dice que ese hijo está un paso arriba. Aquí solo hace falta **existencia** — no enlaces.
- **Bajar** (`descend_T`): `coherent_parents` da que algún **padre** posee `a`, y el padre *sí* es el enlace que `IsChain` pide.

Así que se sube hasta la cima sin enlaces y se baja desde allí con ellos. Eso esquiva el espejo hijos→padres, que no tenemos.

## 3. Lo que sigue fuera: el paso 0, y cuánto cuesta

`reviewSons` barre los pasos `1 .. current_step-2`. Nunca barre el 0. Así que `coherent_sons` **calla en el paso 0** y la subida no puede arrancar ahí — de ahí la hipótesis `1 ≤ a.id.step`.

No es cosmético y no me lo invento: lo medí. `lake exe extend --pickvalid`, 63.314 elecciones permitidas, **3.090 (4,9 %) están en el paso 0**. El enhebrado cubre el 95,1 % de las elecciones que `PickValid` cuantifica, no todas.

Cerrarlo pide una de dos cosas, y las dos son trabajo real:

1. extender la barrida de hijos al paso 0 (cambia el ejecutable, no solo el espejo), o
2. el **otro** espejo de la tabla de hijos —*todo hijo tiene al nodo entre sus padres*—, que es un invariante distinto de `SAbove` y necesitaría la inducción operación por operación que necesitó `SMP`, incluida la parte delicada del desenlace.

## 4. Y lo que faltaría aun con el paso 0 cerrado

Sin adornos, porque es lo que decide si esto sirve: tener el camino enhebrado **no es** `PickValid`. Falta demostrar que ese camino **sobrevive** a la poda tras el pinchazo. Para `cleanInvalid` el argumento está a la vista —los owners fuera del paso pinzado no cambian, y en el pinzado está el ancla, y los vecinos del camino se sostienen entre sí— pero es una inducción sobre `cleanInvalidGo` con el grafo cambiando debajo, y no está escrita.

Recordatorio de por qué esa pasada es la que importa (v41, `--sweep`, 39.984 elecciones): `cleanInvalid` sola **nunca** invalida, y las dos pasadas de coherencia solo quitan nodos en 67 elecciones.

## 5. Estado

| | |
|---|---|
| `SAbove` (todo hijo un paso arriba) | **demostrado**, toda la máquina |
| Enhebrado por debajo del ancla | **demostrado** |
| Enhebrado completo (0 → cima) | **demostrado** para anclas en paso ≥ 1 |
| Anclas en el paso 0 | abierto — 4,9 % de las elecciones |
| Supervivencia del camino a `cleanInvalid` | abierto (la inducción no está escrita) |
| `PickSome` / `PickValid` | abiertos |
| `PairwiseOwned` general | abierto |

---

*Claude (Opus 5), 2026-09-10. `lake build AbsSat` verde, 73 módulos, 0 `sorry`, cierres `[propext, Quot.sound]`.*
