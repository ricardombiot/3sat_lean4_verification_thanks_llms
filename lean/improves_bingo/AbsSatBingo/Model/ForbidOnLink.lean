-- lean/improves_bingo/AbsSatBingo/Model/ForbidOnLink.lean
import AbsSatBingo.Model.ForbidOnChain7BR

/-!
# La restricción a un nodo: el enlace

Los lemas de lado cierran un triángulo con **un** testigo por lado, y las caras de un testigo solo coinciden en lo que
lee su ventana (dos separadores). Por eso un lado no pasa de tres o cuatro bloques (v226, §3, §9). Para cadenas de
cualquier longitud haría falta poder **fijar** el nodo del testigo y seguir dentro del problema fijado, donde el
separador que lee es un extremo fijo y el lado se acorta.

Fijar un nodo `n` es pasar a su **enlace**: lo que forma triángulo con `n`.

* **`LinkR R Tf n`**, **`LinkTf R Tf n`**: las parejas y los tríos prohibidos del enlace.
* **`PinAt φ P0 n`**: las ramas de `P0` que pasan por `n`.
* **`LinkClosedAt φ P0 N lam`** (**la restricción**): para toda estructura cerrada de `P0` y todo nodo `n` del paso `lam`,
  su enlace es una estructura cerrada de `PinAt φ P0 n`.
* **`phantomFree_of_link`** (demostrado): si la restricción vale en el paso `lam`, para no tener familias fantasma basta
  no tenerlas en cada problema fijado en un nodo de `lam`.
* **`phStruct_link`** (demostrado): de los nueve campos de una estructura cerrada, el enlace hereda siete de la
  estructura (los de pareja, del testigo de tríos). Quedan dos, de cuatro nodos: **`LinkTrio`** (el testigo de tríos del
  enlace, un testigo de tetraedros en la estructura) y **`LinkB3`** (todo triángulo del enlace es de una rama que pasa
  por `n`: todo tetraedro con `n` es de una rama).

Lo medido (`probe_exact3.jl`, contador `q_dead`): en los estados de filtro hay tetraedros con un nodo de `σ` que no son
de ninguna rama (48 en `chain6_cross`, 88 en `chain6_bisect`), así que `LinkB3` **falla en el paso `σ`**. Falta saber si
vale en los pasos de los separadores, que son los que acortarían la cadena.
-/

namespace AbsSatBingo.Model

open AbsSatBin.Utils.Alias
open AbsSatBin.Cnf
open AbsSatBin.GraphMap.CnfMapBin
open AbsSatBin.GraphMap.CnfSelBin

namespace GPathB

variable {φ : Cnf} {P0 P : Assign → Prop} {N σ : Int}

/-- Las parejas del enlace de `n`: forman con `n` un triángulo sin prohibir (o uno degenerado). -/
def LinkR (R : PathNodeId → PathNodeId → Prop) (Tf : Trios) (n : PathNodeId) (y w : PathNodeId) : Prop :=
  R y w ∧ R y n ∧ R w n ∧ (y = w ∨ y = n ∨ w = n ∨ ¬ Tf y w n)

/-- Los tríos prohibidos del enlace de `n`: el propio trío, o una de sus caras con `n` (si no es degenerada). -/
def LinkTf (Tf : Trios) (n : PathNodeId) : Trios := fun x u w =>
  Tf x u w ∨ (x ≠ n ∧ u ≠ n ∧ Tf x u n) ∨ (x ≠ n ∧ w ≠ n ∧ Tf x w n) ∨ (u ≠ n ∧ w ≠ n ∧ Tf u w n)

/-- Las ramas de `P0` que pasan por `n`. -/
def PinAt (φ : Cnf) (P0 : Assign → Prop) (n : PathNodeId) (a : Assign) : Prop :=
  P0 a ∧ pidOfAssign φ a n.id.step = n

/-- **La restricción**: el enlace de todo nodo del paso `lam` de una estructura cerrada es una estructura cerrada para
las ramas que pasan por él. -/
def LinkClosedAt (φ : Cnf) (P0 : Assign → Prop) (N lam : Int) : Prop :=
  ∀ (R : PathNodeId → PathNodeId → Prop) (Tf : Trios), PhStruct φ P0 N R Tf →
    ∀ n : PathNodeId, n.id.step = lam → R n n → PhStruct φ (PinAt φ P0 n) N (LinkR R Tf n) (LinkTf Tf n)

theorem triOf_of_pin {P : Assign → Prop} {n x u w : PathNodeId} (h : TriOf φ (PinAt φ P n) x u w) :
    TriOf φ P x u w := by
  obtain ⟨a, ha, h1, h2, h3⟩ := h
  exact ⟨a, ha.1, h1, h2, h3⟩

/-- **La reducción**: con la restricción en el paso `lam`, basta que no haya familias fantasma en cada problema fijado
en un nodo de `lam`. -/
theorem phantomFree_of_link {lam : Int} (h0 : 0 ≤ lam) (hN : lam < N) (hL : LinkClosedAt φ P0 N lam)
    (hPF : ∀ n : PathNodeId, n.id.step = lam → PhantomFree φ (PinAt φ P0 n) (PinAt φ P n) N σ) :
    PhantomFree φ P0 P N σ := by
  intro R Tf hrefl hsymm hsw23 hsw12 hsteps hpair htrio hb2 hb3 hanch
  have hS : PhStruct φ P0 N R Tf := ⟨hrefl, hsymm, hsw23, hsw12, hsteps, hpair, htrio, hb2, hb3⟩
  -- el problema fijado en `n`, sobre el enlace
  have sub : ∀ n : PathNodeId, n.id.step = lam → R n n →
      (∀ y w, LinkR R Tf n y w → ∃ a, PinAt φ P n a ∧ pidOfAssign φ a y.id.step = y ∧
        pidOfAssign φ a w.id.step = w) ∧
      (∀ x u w, LinkR R Tf n x u → LinkR R Tf n x w → LinkR R Tf n u w → x ≠ u → x ≠ w → u ≠ w →
        ¬ LinkTf Tf n x u w → TriOf φ (PinAt φ P n) x u w) := by
    intro n hn hnn
    have L := hL R Tf hS n hn hnn
    obtain ⟨c2, c3⟩ := hPF n hn (LinkR R Tf n) (LinkTf Tf n) L.refl L.symm L.sw23 L.sw12 L.steps L.pair L.trio
      L.b2 L.b3 (fun a s ha hs hst hp => ⟨hanch a s ha.1 hs.1 hst hp, ha.2⟩)
    exact ⟨c2, fun x u w a b c d e f g => c3 x u w a b c d e f g⟩
  -- un trío que no prohibe una cara degenerada
  have nf_rot : ∀ {x u w : PathNodeId}, Tri R Tf x u w → ¬ Tf u w x := fun {x u w} t h =>
    t.nf (hS.sw12 u x w (hS.symm _ _ t.xu) t.uw t.xw (hS.sw23 u w x t.uw (hS.symm _ _ t.xu) (hS.symm _ _ t.xw) h))
  -- un triángulo está en el enlace de su primer nodo
  have self : ∀ {x u w : PathNodeId}, Tri R Tf x u w → x.id.step = lam → TriOf φ P x u w := by
    intro x u w t hx
    have hxx : R x x := (hrefl _ _ t.xu).1
    exact triOf_of_pin ((sub x hx hxx).2 x u w ⟨t.xu, hxx, hsymm _ _ t.xu, Or.inr (Or.inl rfl)⟩
      ⟨t.xw, hxx, hsymm _ _ t.xw, Or.inr (Or.inl rfl)⟩ ⟨t.uw, hsymm _ _ t.xu, hsymm _ _ t.xw, Or.inr (Or.inr (Or.inr
        (nf_rot t)))⟩ t.nxu t.nxw t.nuw (by
      rintro (h | ⟨a1, _, _⟩ | ⟨a1, _, _⟩ | ⟨_, _, h⟩)
      · exact t.nf h
      · exact a1 rfl
      · exact a1 rfl
      · exact nf_rot t h))
  refine ⟨fun y w hyw => ?_, fun x u w hxu hxw huw nxu nxw nuw hn => ?_⟩
  · -- una pareja: el nodo del paso `lam` que la completa
    obtain ⟨s, hss, hys, hws, hor⟩ := hpair y w hyw lam h0 hN
    obtain ⟨a, ha, h1, h2⟩ := (sub s hss (hrefl y s hys).2).1 y w
      ⟨hyw, hys, hws, by rcases hor with e | e | e | e
                         · exact Or.inl e
                         · exact Or.inr (Or.inl e.symm)
                         · exact Or.inr (Or.inr (Or.inl e.symm))
                         · exact Or.inr (Or.inr (Or.inr e))⟩
    exact ⟨a, ha.1, h1, h2⟩
  · -- un triángulo: su testigo del paso `lam`
    have t : Tri R Tf x u w := ⟨hxu, hxw, huw, nxu, nxw, nuw, hn⟩
    obtain ⟨n, hns, hor⟩ := t.wit hS h0 hN
    rcases hor with e | ⟨t1, t2, t3⟩
    · -- el testigo es un nodo del triángulo: el enlace de ese nodo
      rcases e with e | e | e
      · exact self t (e ▸ hns)
      · exact (self (t.swap12 hS) (e ▸ hns)).swap12
      · exact ((self ((t.swap23 hS).swap12 hS) (e ▸ hns)).swap12).swap23
    · -- las tres caras con el testigo: el triángulo está en el enlace
      have hnn : R n n := (hrefl _ _ t1.xw).2
      refine triOf_of_pin ((sub n hns hnn).2 x u w ⟨hxu, t1.xw, t1.uw, Or.inr (Or.inr (Or.inr t1.nf))⟩
        ⟨hxw, t2.xw, t2.uw, Or.inr (Or.inr (Or.inr t2.nf))⟩ ⟨huw, t3.xw, t3.uw, Or.inr (Or.inr (Or.inr t3.nf))⟩
        nxu nxw nuw ?_)
      rintro (h | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩)
      · exact hn h
      · exact t1.nf h
      · exact t2.nf h
      · exact t3.nf h

/-! ## Lo que el enlace hereda, y lo que falta -/

/-- **El testigo de tríos del enlace**: un tetraedro de la estructura (un triángulo del enlace) tiene en cada paso un
nodo que lo completa sin prohibir. -/
def LinkTrio (R : PathNodeId → PathNodeId → Prop) (Tf : Trios) (n : PathNodeId) (N : Int) : Prop :=
  ∀ x u w, LinkR R Tf n x u → LinkR R Tf n x w → LinkR R Tf n u w → x ≠ u → x ≠ w → u ≠ w →
    ¬ LinkTf Tf n x u w → ∀ l, 0 ≤ l → l < N →
      ∃ s, s.id.step = l ∧ LinkR R Tf n x s ∧ LinkR R Tf n u s ∧ LinkR R Tf n w s ∧
        (s = x ∨ s = u ∨ s = w ∨ (¬ LinkTf Tf n x u s ∧ ¬ LinkTf Tf n x w s ∧ ¬ LinkTf Tf n u w s))

/-- **Todo triángulo del enlace es de una rama que pasa por `n`**: todo tetraedro con `n` es de una rama. -/
def LinkB3 (φ : Cnf) (P0 : Assign → Prop) (R : PathNodeId → PathNodeId → Prop) (Tf : Trios) (n : PathNodeId) :
    Prop :=
  ∀ x u w, LinkR R Tf n x u → LinkR R Tf n x w → LinkR R Tf n u w → x ≠ u → x ≠ w → u ≠ w →
    ¬ LinkTf Tf n x u w → ∃ a, PinAt φ P0 n a ∧ pidOfAssign φ a x.id.step = x ∧ pidOfAssign φ a u.id.step = u ∧
      pidOfAssign φ a w.id.step = w

/-- **El enlace es una estructura cerrada si tiene sus dos campos de cuatro nodos**: los otros siete los hereda (las
parejas del enlace, del testigo de tríos de la estructura y de sus ramas). -/
theorem phStruct_link {R : PathNodeId → PathNodeId → Prop} {Tf : Trios} (hS : PhStruct φ P0 N R Tf)
    {n : PathNodeId} (hnn : R n n) (htr : LinkTrio R Tf n N) (hb3 : LinkB3 φ P0 R Tf n) :
    PhStruct φ (PinAt φ P0 n) N (LinkR R Tf n) (LinkTf Tf n) := by
  -- girar un trío prohibido de la estructura
  have r23 : ∀ {a b r}, R a b → R a r → R b r → Tf a r b → Tf a b r := fun {a b r} h1 h2 h3 h =>
    hS.sw23 a r b h2 h1 (hS.symm _ _ h3) h
  have r12 : ∀ {a b r}, R a b → R a r → R b r → Tf b a r → Tf a b r := fun {a b r} h1 h2 h3 h =>
    hS.sw12 b a r (hS.symm _ _ h1) h3 h2 h
  refine ⟨fun y w h => ⟨⟨(hS.refl _ _ h.1).1, h.2.1, h.2.1, Or.inl rfl⟩, ⟨(hS.refl _ _ h.1).2, h.2.2.1, h.2.2.1,
    Or.inl rfl⟩⟩, fun y w h => ⟨hS.symm _ _ h.1, h.2.2.1, h.2.1, ?_⟩, fun a b r hab har hbr h => ?_,
    fun a b r hab har hbr h => ?_, fun y w h => hS.steps y w h.1, fun y w h l l0 lN => ?_, htr,
    fun y w h => ?_, hb3⟩
  · -- simetría
    rcases h.2.2.2 with e | e | e | e
    · exact Or.inl e.symm
    · exact Or.inr (Or.inr (Or.inl e))
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inr (fun h' => e (r12 h.1 h.2.1 h.2.2.1 h'))))
  · -- girar los dos últimos
    rcases h with h | ⟨a1, a2, h⟩ | ⟨a1, a2, h⟩ | ⟨a1, a2, h⟩
    · exact Or.inl (hS.sw23 a b r hab.1 har.1 hbr.1 h)
    · exact Or.inr (Or.inr (Or.inl ⟨a1, a2, h⟩))
    · exact Or.inr (Or.inl ⟨a1, a2, h⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨a2, a1, hS.sw12 b r n hbr.1 hab.2.2.1 har.2.2.1 h⟩))
  · -- girar los dos primeros
    rcases h with h | ⟨a1, a2, h⟩ | ⟨a1, a2, h⟩ | ⟨a1, a2, h⟩
    · exact Or.inl (hS.sw12 a b r hab.1 har.1 hbr.1 h)
    · exact Or.inr (Or.inl ⟨a2, a1, hS.sw12 a b n hab.1 hab.2.1 hab.2.2.1 h⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨a1, a2, h⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨a1, a2, h⟩))
  · -- el testigo de parejas del enlace, del de tríos (o de parejas) de la estructura
    obtain ⟨hyw, hyn, hwn, hd⟩ := h
    by_cases eyw : y = w
    · -- degenerada: el testigo de la pareja `(y, n)`
      subst eyw
      obtain ⟨s, hss, hys, hns, hor⟩ := hS.pair y n hyn l l0 lN
      have ls : LinkR R Tf n y s := ⟨hys, hyn, hS.symm _ _ hns, by
        rcases hor with e | e | e | e
        · exact Or.inr (Or.inl e)
        · exact Or.inl e.symm
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inr (Or.inr (Or.inr (fun h' => e (r23 hyn hys hns h'))))⟩
      exact ⟨s, hss, ls, ls, Or.inl rfl⟩
    by_cases eyn : y = n
    · -- `y = n`: el testigo de la pareja `(n, w)`
      subst eyn
      obtain ⟨s, hss, hys, hws, hor⟩ := hS.pair y w hyw l l0 lN
      refine ⟨s, hss, ⟨hys, hnn, hS.symm _ _ hys, Or.inr (Or.inl rfl)⟩, ⟨hws, hwn, hS.symm _ _ hys, ?_⟩, ?_⟩
      · rcases hor with e | e | e | e
        · exact absurd e eyw
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inl e.symm
        · exact Or.inr (Or.inr (Or.inr (fun h' =>
            e (r12 hyw hys hws (r23 (hS.symm _ _ hyw) hws hys h')))))
      · rcases hor with e | e | e | e
        · exact absurd e eyw
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (Or.inl e))
        · refine Or.inr (Or.inr (Or.inr ?_))
          rintro (h' | ⟨a1, _, _⟩ | ⟨a1, _, _⟩ | ⟨_, a2, h'⟩)
          · exact e h'
          · exact a1 rfl
          · exact a1 rfl
          · exact e (r12 hyw hys hws (r23 (hS.symm _ _ hyw) hws hys h'))
    by_cases ewn : w = n
    · -- `w = n`: el testigo de la pareja `(y, n)`
      subst ewn
      obtain ⟨s, hss, hys, hws, hor⟩ := hS.pair y w hyw l l0 lN
      refine ⟨s, hss, ⟨hys, hyw, hS.symm _ _ hws, ?_⟩, ⟨hws, hnn, hS.symm _ _ hws, Or.inr (Or.inl rfl)⟩, ?_⟩
      · rcases hor with e | e | e | e
        · exact absurd e eyw
        · exact Or.inl e.symm
        · exact Or.inr (Or.inr (Or.inl e))
        · exact Or.inr (Or.inr (Or.inr (fun h' => e (r23 hyw hys hws h'))))
      · rcases hor with e | e | e | e
        · exact absurd e eyw
        · exact Or.inr (Or.inl e)
        · exact Or.inr (Or.inr (Or.inl e))
        · refine Or.inr (Or.inr (Or.inr ?_))
          rintro (h' | ⟨_, a2, _⟩ | ⟨_, a2, h'⟩ | ⟨a1, _, _⟩)
          · exact e h'
          · exact a2 rfl
          · exact e (r23 hyw hys hws h')
          · exact a1 rfl
    · -- el caso general: el testigo del trío `(y, w, n)`
      have nf : ¬ Tf y w n := by
        rcases hd with e | e | e | e
        · exact absurd e eyw
        · exact absurd e eyn
        · exact absurd e ewn
        · exact e
      obtain ⟨s, hss, hys, hws, hns, hor⟩ := hS.trio y w n hyw hyn hwn eyw eyn ewn nf l l0 lN
      have hsn := hS.symm _ _ hns
      rcases hor with e | e | e | ⟨f1, f2, f3⟩
      · subst e
        exact ⟨_, hss, ⟨hys, hyn, hyn, Or.inl rfl⟩, ⟨hws, hwn, hyn, Or.inr (Or.inr (Or.inr
          (fun h' => nf (r12 hyw hyn hwn h'))))⟩, Or.inr (Or.inl rfl)⟩
      · subst e
        exact ⟨_, hss, ⟨hys, hyn, hwn, Or.inr (Or.inr (Or.inr nf))⟩, ⟨hws, hwn, hwn, Or.inl rfl⟩,
          Or.inr (Or.inr (Or.inl rfl))⟩
      · subst e
        refine ⟨s, hss, ⟨hys, hyn, hsn, Or.inr (Or.inr (Or.inl rfl))⟩, ⟨hws, hwn, hsn, Or.inr (Or.inr (Or.inl rfl))⟩,
          Or.inr (Or.inr (Or.inr ?_))⟩
        rintro (h' | ⟨_, _, h'⟩ | ⟨_, a2, _⟩ | ⟨_, a2, _⟩)
        · exact nf h'
        · exact nf h'
        · exact a2 rfl
        · exact a2 rfl
      · refine ⟨s, hss, ⟨hys, hyn, hsn, Or.inr (Or.inr (Or.inr (fun h' => f2 (r23 hyn hys hns h'))))⟩,
          ⟨hws, hwn, hsn, Or.inr (Or.inr (Or.inr (fun h' => f3 (r23 hwn hws hns h'))))⟩, Or.inr (Or.inr (Or.inr ?_))⟩
        rintro (h' | ⟨_, _, h'⟩ | ⟨_, _, h'⟩ | ⟨_, _, h'⟩)
        · exact f1 h'
        · exact nf h'
        · exact f2 (r23 hyn hys hns h')
        · exact f3 (r23 hwn hws hns h')
  · -- las parejas del enlace son de ramas que pasan por `n`
    obtain ⟨hyw, hyn, hwn, hd⟩ := h
    by_cases eyw : y = w
    · subst eyw
      obtain ⟨a, ha, h1, h2⟩ := hS.b2 y n hyn
      exact ⟨a, ⟨ha, h2⟩, h1, h1⟩
    by_cases eyn : y = n
    · subst eyn
      obtain ⟨a, ha, h1, h2⟩ := hS.b2 _ _ hyw
      exact ⟨a, ⟨ha, h1⟩, h1, h2⟩
    by_cases ewn : w = n
    · subst ewn
      obtain ⟨a, ha, h1, h2⟩ := hS.b2 _ _ hyw
      exact ⟨a, ⟨ha, h2⟩, h1, h2⟩
    · have nf : ¬ Tf y w n := by
        rcases hd with e | e | e | e
        · exact absurd e eyw
        · exact absurd e eyn
        · exact absurd e ewn
        · exact e
      obtain ⟨a, ha, h1, h2, h3⟩ := hS.b3 y w n hyw hyn hwn eyw eyn ewn nf
      exact ⟨a, ⟨ha, h3⟩, h1, h2⟩

end GPathB

end AbsSatBingo.Model
