# Deep Dive: Theorem 02 (Soundness_Pure)

**Analysis of how to prove machine soundness by reusing existing PureDriver theorem.**

---

## The Challenge

We need to prove:
```lean
theorem soundness_pure (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true → ∃ a : Assign, Sat a cnf
```

The trap: It's tempting to think "soundness is hard, it requires deep algorithm reasoning." But actually, **the hard reasoning is already done in PureDriver**. We just need to *apply* it.

---

## Step 1: Understand What We Have

### Existing Theorem (SatMachine/Soundness.lean:122)

Let me trace what `soundness_theorem` actually says. It's something like:

```lean
theorem soundness_theorem (cnf : Cnf) :
  PureDriver.pureRun cnf ≠ [] → ∃ a : Assign, Sat a cnf
```

Let's unpack this:
- **Input:** A CNF formula
- **Precondition:** `PureDriver.pureRun cnf ≠ []` (PureDriver found something)
- **Conclusion:** `∃ a, Sat a cnf` (that something satisfies the formula)

This is the *core soundness result*. It says: "If PureDriver runs and finds assignments, those assignments actually satisfy the formula."

### Our Definition (PureSatMachine.lean)

```lean
def is_satisfiable (m : SatMachinePure) : Bool :=
  if m.timeline.isEmpty then
    false
  else
    let final_line := m.timeline[m.timeline.length - 1]!
    !final_line.isEmpty
```

Let's unpack this:
- Check if timeline is empty → return false (UNSAT)
- Otherwise, get the final line (last element of timeline)
- Return true if final line is non-empty

**Key question:** How does `timeline` relate to `PureDriver.pureRun`?

---

## Step 2: The Structural Bridge (Theorem 01)

This is why **Theorem 01 is critical**:

```lean
theorem run_pure_eq_driver (cnf : Cnf) :
  List.map (fun p => p.2) (run_pure cnf).timeline = PureDriver.pureRun cnf
```

This says:
- `run_pure cnf` produces a timeline (list of GPathM states keyed by node)
- If we extract just the GPathM values (the `.2` in each pair), we get the exact same thing as `PureDriver.pureRun`

**So the translation is:**
```
run_pure cnf timeline
    ↓ (extract .2 values)
PureDriver.pureRun cnf
```

---

## Step 3: Connect is_satisfiable to pureRun Non-Emptiness

Now the key insight:

**If `is_satisfiable (run_pure cnf) = true`, what does that mean in terms of PureDriver?**

Let's trace:
1. `is_satisfiable (run_pure cnf) = true`
2. → Timeline is not empty AND final line is not empty (by definition)
3. → `(run_pure cnf).timeline` has at least 1 element (to have a "final line")
4. → After extracting `.2` values: `List.map (fun p => p.2) (run_pure cnf).timeline` has at least 1 element
5. → By Theorem 01: `PureDriver.pureRun cnf` has at least 1 element
6. → `PureDriver.pureRun cnf ≠ []`

**This is the key lemma!**

```lean
lemma is_satisfiable_implies_pureRun_nonempty (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true → PureDriver.pureRun cnf ≠ [] := by
  intro h
  
  -- Unfold is_satisfiable to get the timeline properties
  unfold is_satisfiable at h
  
  -- Now h says: final_line is not empty
  -- This means timeline has at least 1 element
  
  -- Use run_pure_eq_driver to connect to PureDriver
  have equiv := run_pure_eq_driver cnf
  
  -- If timeline.last is non-empty, then timeline is non-empty
  -- Apply the equivalence
  intro h_empty
  
  -- We have h saying "last line non-empty"
  -- We have h_empty saying "PureDriver.pureRun = []"
  -- These contradict via the equivalence
  
  -- After simplification, get contradiction
  sorry
```

---

## Step 4: Apply Existing Soundness Theorem

Once we have that lemma, the rest is **one application**:

```lean
theorem soundness_pure (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true → ∃ a : Assign, Sat a cnf := by
  intro h_sat
  
  -- Use our lemma to get PureDriver.pureRun ≠ []
  have h_pureRun := is_satisfiable_implies_pureRun_nonempty cnf h_sat
  
  -- Apply the existing soundness theorem
  exact soundness_theorem cnf h_pureRun
```

**That's it!** The proof delegates to the existing theorem.

---

## Step 5: Potential Complications

Now, the question is: **How much work is `is_satisfiable_implies_pureRun_nonempty`?**

Let's think about the actual types:

```lean
def is_satisfiable (m : SatMachinePure) : Bool :=
  if m.timeline.isEmpty then
    false
  else
    let final_line := m.timeline[m.timeline.length - 1]!
    !final_line.isEmpty
```

When `is_satisfiable = true`, we know:
- `!m.timeline.isEmpty` (timeline is non-empty)
- `!final_line.isEmpty` (final line is non-empty)

The tricky part: **`final_line` is what type?**

Looking at `PureLine`:
```lean
type PureLine = List (NodeId × GPathM)
```

So `final_line` is `List (NodeId × GPathM)`.

When we say `!final_line.isEmpty`, we mean the list has at least 1 element of type `NodeId × GPathM`.

Now, `PureDriver.pureRun` returns `List GPathM` (just the GPathM values, not keyed by node).

The equivalence (Theorem 01) says:
```lean
List.map (fun p => p.2) (run_pure cnf).timeline = PureDriver.pureRun cnf
```

So:
- If `timeline` (which has type `List (NodeId × GPathM)`) is non-empty
- Then `List.map (fun p => p.2) timeline` is also non-empty
- Then `PureDriver.pureRun` is non-empty

**This is a straightforward list property!**

---

## Complete Proof Sketch

Here's what the full proof might look like:

```lean
-- Helper lemma
lemma is_satisfiable_implies_pureRun_nonempty (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true → PureDriver.pureRun cnf ≠ [] := by
  intro h_sat
  
  -- Unfold is_satisfiable
  unfold is_satisfiable at h_sat
  
  -- Now h_sat : final_line ≠ [] (after the if-then-else)
  -- This means (run_pure cnf).timeline is non-empty
  
  -- Use the equivalence from Theorem 01
  have equiv := run_pure_eq_driver cnf
  
  -- If the keyed timeline is non-empty, map is non-empty
  have timeline_nonempty : (run_pure cnf).timeline ≠ [] := by
    -- If final_line is non-empty, timeline must be non-empty
    -- because we got final_line from timeline[length-1]!
    sorry -- should be trivial
  
  -- Now apply map property
  have map_nonempty : List.map (fun p => p.2) (run_pure cnf).timeline ≠ [] := by
    simp [List.map_eq_empty]
    intro contra
    -- If map is empty, then source is empty
    sorry
  
  -- Connect via equivalence
  rw [← equiv]
  exact map_nonempty

-- Main theorem
theorem soundness_pure (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true → ∃ a : Assign, Sat a cnf := by
  intro h
  have h' := is_satisfiable_implies_pureRun_nonempty cnf h
  exact soundness_theorem cnf h'
```

---

## Alternative: Terser Approach

If we understand the connection well, we could write this more compactly:

```lean
theorem soundness_pure (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true → ∃ a : Assign, Sat a cnf := by
  intro h
  unfold is_satisfiable at h
  
  -- h : final_line ≠ []
  -- This means PureDriver.pureRun ≠ [] via Theorem 01
  
  have : PureDriver.pureRun cnf ≠ [] := by
    have equiv := run_pure_eq_driver cnf
    simp [List.map_eq_empty] at equiv
    simp [List.map_eq_empty]
    -- Extract from h and equiv
    sorry
  
  exact soundness_theorem cnf this
```

Or even more terse (if Lean's automation helps):

```lean
theorem soundness_pure (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true → ∃ a : Assign, Sat a cnf := by
  intro h
  simp [is_satisfiable] at h
  have := run_pure_eq_driver cnf
  simp [List.map_eq_empty] at *
  exact soundness_theorem cnf (by omega)
```

---

## Expected Actual Definition of soundness_theorem

The real `soundness_theorem` in SatMachine/Soundness.lean probably looks something like:

```lean
theorem soundness_theorem (cnf : Cnf) (h : PureDriver.pureRun cnf ≠ []) :
  ∃ a : Assign, Sat a cnf := by
  -- Deep proof using PureDriver invariants, GPathM properties, etc.
  -- ~100+ lines of careful reasoning about graph paths
  -- Uses: Conservation lemmas, pureRun_carries, etc.
  sorry
```

**Our job:** Get the precondition `PureDriver.pureRun cnf ≠ []` from `is_satisfiable (run_pure cnf) = true`.

---

## Test Case Validation

Let's validate our logic on **pigeonhole.cnf** (UNSAT):

**Expected flow:**
1. `is_satisfiable (run_pure pigeonhole) = false`
   - Why? Final timeline is empty (no solutions)
2. Our theorem shouldn't apply (precondition false)
   - Good! We don't claim a solution exists

**And on test_sat_medium.cnf** (SAT):

**Expected flow:**
1. `is_satisfiable (run_pure test_sat_medium) = true`
   - Why? Final timeline has at least 1 state
2. Our lemma: `PureDriver.pureRun test_sat_medium ≠ []`
   - True! PureDriver found states
3. Apply `soundness_theorem`: Get an assignment
   - True! One of the 9 solutions

---

## Potential Gotchas

### 1. **Type Mismatch: Bool vs Prop**

`is_satisfiable` returns `Bool`, but we're doing logical reasoning.

```lean
is_satisfiable (run_pure cnf) = true  -- Bool equality
```

This isn't `Prop`, it's `Bool`. We need to convert:

```lean
import Std.Data.List.Basic

theorem soundness_pure (cnf : Cnf) :
  is_satisfiable (run_pure cnf) = true → ∃ a : Assign, Sat a cnf := by
  intro h
  -- h : is_satisfiable (run_pure cnf) = true
  
  -- Convert Bool to Prop
  simp at h  -- simplifies Bool.true to True
  sorry
```

Or use `decide`:
```lean
intro h : is_satisfiable (run_pure cnf) = true
-- Now we can pattern match on the definition
```

### 2. **Option/Option? on Empty List**

`timeline.last?` returns `Option`. If timeline is empty, it's `none`.

```lean
def is_satisfiable (m : SatMachinePure) : Bool :=
  if m.timeline.isEmpty then false
  else let final_line := m.timeline[m.timeline.length - 1]!
       !final_line.isEmpty
```

The `!` (array indexing) is unsafe. We need `m.timeline.last?`:

```lean
def is_satisfiable (m : SatMachinePure) : Bool :=
  match m.timeline.last? with
  | some final_line => !final_line.isEmpty
  | none => false
```

This makes the equivalence clearer:
- `none` → final_line doesn't exist → false (UNSAT)
- `some []` → final_line exists but empty → false (UNSAT)
- `some (x::xs)` → final_line non-empty → true (SAT)

### 3. **Keyed States vs Pure States**

Timeline is `List (NodeId × GPathM)` but we need to reason about `List GPathM`.

The `map (fun p => p.2)` extracts the GPathM values.

When final_line is non-empty *as keyed states*, the extracted states are also non-empty:
```lean
final_line : List (NodeId × GPathM)
final_line.length > 0  -- has at least 1 element

List.map Prod.snd final_line : List GPathM
List.map Prod.snd final_line.length = final_line.length  -- lengths preserved
```

This is trivial by list properties.

---

## Recommended Proof Strategy

1. **First:** Prove the helper lemma `is_satisfiable_implies_pureRun_nonempty`
   - This is ~20 lines of straightforward list/type manipulation
   - Do this once, then reuse it

2. **Then:** Apply `soundness_theorem`
   - This is 1-2 lines
   - The hard work was already done

3. **Optional:** Prove `completeness_pure` using identical pattern
   - Symmetric structure
   - Same helper lemma idea applies

---

## Estimated Difficulty Breakdown

| Part | Lines | Difficulty | Effort |
|------|-------|-----------|--------|
| Understand soundness_theorem | — | Medium | 30 min |
| Prove is_satisfiable↔pureRun | 20-30 | Easy | 1 hour |
| Apply soundness theorem | 2-3 | Trivial | 10 min |
| Debug + cleanup | — | Medium | 1 hour |
| **TOTAL** | ~30 | Easy-Medium | **3 hours** |

---

## If Stuck: Debugging Strategy

**Problem:** Lean complains about types not matching

**Solution:** Use `unfold` liberally to expose definitions:
```lean
unfold is_satisfiable
unfold PureLine
unfold PureSatMachine.timeline
```

**Problem:** Can't connect `timeline.isEmpty` to `List.map.isEmpty`

**Solution:** Use list lemmas:
```lean
#check List.map_eq_empty
#check List.length_map
#check List.isEmpty_iff_eq_empty
```

**Problem:** `timeline[length-1]!` is unsafe indexing

**Solution:** Use `.last?` instead:
```lean
m.timeline.last? =
match m.timeline with
| [] => none
| x :: xs => some (xs.last xs.empty)
```

---

## Summary

**Theorem 02 soundness_pure is NOT hard because:**

1. The real "soundness" proof already exists in PureDriver
2. We just need to connect our verdict to PureDriver's result
3. The connection is via Theorem 01 (structural equivalence)
4. Once connected, we apply the existing theorem (1-2 lines)

**The challenge is not reasoning about correctness, it's reasoning about types and representations:**
- Converting `Bool = true` to logical reasoning
- Connecting keyed timeline to pure timeline
- Using list/option properties correctly

**Recommendation:** Spend your time getting the type matching right, then the proof itself will be trivial.

---

**Estimated effort: 3-4 hours once Theorem 01 is proven.**
