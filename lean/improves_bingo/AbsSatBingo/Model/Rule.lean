-- lean/improves_bingo/AbsSatBingo/Model/Rule.lean
import AbsSatBingo.Model.Reader

/-!
# El marco de reglas (fase L6, parte 4)

Una **regla** es un operador sobre `GPathB` con tres obligaciones:

* `shrinks` — solo borra y no sube la medida (`Shrinks`), lo que da la terminación;
* `keeps` — conserva toda camarilla llevada (`Carried`), lo que da que no se pierde ninguna solución;
* `docs` — conserva `AliveDocs`, lo que da el combustible del lector.

Las reglas del review de hoy son instancias (`purge`, `pairs`, `links`, `parents`, `sons`, `pass`, `review`), y se
componen (`Rule.comp`) y se iteran con combustible (`Rule.fuel`). Una regla nueva sobre aristas (informe v199 §6)
entra en el review demostrando estas tres cosas; lo que la hace **útil** es que acerque los estados a `NoZombie`,
la única hipótesis de `readG_isSome_of_noZombie`.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias

namespace GPathB

structure Rule where
  apply   : GPathB → GPathB
  shrinks : ∀ g, Shrinks (apply g) g
  keeps   : ∀ g (S : Int → PathNodeId), Carried g S → Carried (apply g) S
  docs    : ∀ g, AliveDocs g → AliveDocs (apply g)

namespace Rule

/-- Primero `r₁`, después `r₂`. -/
def comp (r₂ r₁ : Rule) : Rule where
  apply g := r₂.apply (r₁.apply g)
  shrinks g := (r₂.shrinks _).trans (r₁.shrinks g)
  keeps g S h := r₂.keeps _ S (r₁.keeps g S h)
  docs g h := r₂.docs _ (r₁.docs g h)

/-- La regla que no hace nada. -/
def id : Rule where
  apply g := g
  shrinks g := Shrinks.refl g
  keeps _ _ h := h
  docs _ h := h

/-- `r` mientras el gpath es válido y la vuelta baja la medida, con `n` vueltas como mucho. -/
def fuelApply (r : Rule) : Nat → GPathB → GPathB
  | 0, g => g
  | n + 1, g =>
    if g.isValid then
      let g' := r.apply g
      if g'.measure < g.measure then fuelApply r n g' else g'
    else g

theorem fuelApply_spec (r : Rule) : ∀ (n : Nat) (g : GPathB),
    Shrinks (r.fuelApply n g) g ∧ (∀ S, Carried g S → Carried (r.fuelApply n g) S) ∧
      (AliveDocs g → AliveDocs (r.fuelApply n g)) := by
  intro n
  induction n with
  | zero => intro g; exact ⟨Shrinks.refl g, fun _ h => h, fun h => h⟩
  | succ n ih =>
    intro g
    simp only [fuelApply]
    split
    · split
      · obtain ⟨h1, h2, h3⟩ := ih (r.apply g)
        exact ⟨h1.trans (r.shrinks g), fun S h => h2 S (r.keeps g S h), fun h => h3 (r.docs g h)⟩
      · exact ⟨r.shrinks g, r.keeps g, r.docs g⟩
    · exact ⟨Shrinks.refl g, fun _ h => h, fun h => h⟩

/-- **`r` hasta su punto fijo** (`measure + 1` vueltas bastan: cada una que sigue baja la medida). -/
def fuel (r : Rule) : Rule where
  apply g := r.fuelApply (g.measure + 1) g
  shrinks g := (fuelApply_spec r _ g).1
  keeps g S h := (fuelApply_spec r _ g).2.1 S h
  docs g h := (fuelApply_spec r _ g).2.2 h

end Rule

-- ============================================================
-- Las reglas de hoy
-- ============================================================

theorem aliveDocs_reviewParents {g : GPathB} (h : AliveDocs g) : AliveDocs g.reviewParents := by
  unfold reviewParents; split
  · exact aliveDocs_reviewSteps _ _ _ h
  · exact h

theorem aliveDocs_reviewSons {g : GPathB} (h : AliveDocs g) : AliveDocs g.reviewSons := by
  unfold reviewSons; split
  · exact aliveDocs_reviewSteps _ _ _ h
  · exact h

/-- La purga (Julia `clean_invalid_nodes!`). -/
def Rule.purge : Rule := ⟨clean, shrinks_clean, fun _ _ h => carried_clean h, fun _ h => aliveDocs_clean h⟩

/-- La purga y la regla de parejas. -/
def Rule.pairs : Rule :=
  ⟨cleanPair, shrinks_cleanPair, fun _ _ h => carried_cleanPair h,
   fun _ h => aliveDocs_pairFuel _ _ (aliveDocs_clean h)⟩

/-- Los enlaces caducados. -/
def Rule.links : Rule :=
  ⟨pruneLinks, shrinks_pruneLinks, fun _ _ h => carried_pruneLinks h, fun _ h => aliveDocs_pruneLinks h⟩

/-- La pasada de padres. -/
def Rule.parents : Rule :=
  ⟨reviewParents, shrinks_reviewParents, fun _ _ h => carried_reviewParents h,
   fun _ h => aliveDocs_reviewParents h⟩

/-- La pasada de hijos. -/
def Rule.sons : Rule :=
  ⟨reviewSons, shrinks_reviewSons, fun _ _ h => carried_reviewSons h, fun _ h => aliveDocs_reviewSons h⟩

/-- Una vuelta del review, como composición de las reglas (su `apply` es `reviewPass`, por definición). -/
def Rule.pass : Rule := Rule.links.comp (Rule.sons.comp (Rule.parents.comp (Rule.links.comp Rule.pairs)))

/-- El review de la máquina (con `dirty`, como Julia). -/
def Rule.review : Rule :=
  ⟨GPathB.review, shrinks_review, fun _ _ h => carried_review h, fun _ h => aliveDocs_review h⟩

end GPathB

end AbsSatBingo.Model
