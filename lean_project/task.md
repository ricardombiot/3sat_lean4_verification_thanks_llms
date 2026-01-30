# Phase 2: Algorithm Migration & Verification

- [x] **Migrate GraphPath Logic** <!-- id: 0 -->
    - [x] Remove `PathCollectionLines` placeholder in `GraphPath.lean` and import `AbsSat.Db.Path.Cols.PathColLines`. <!-- id: 1 -->
    - [x] Implement `do_up!` and `do_up_filtering!` in `GraphPath.lean` (porting logic from Julia `graph_path_up.jl` / `filter.jl`). <!-- id: 2 -->
    - [x] Verify `GraphPath` can support `SatMachine` operations. <!-- id: 3 -->
- [x] **Migrate SatMachine** <!-- id: 4 -->
    - [x] Create `AbsSat/SatMachine` directory. <!-- id: 5 -->
    - [x] Create `AbsSat/SatMachine/SatMachine.lean`. <!-- id: 6 -->
    - [x] Implement `MSat` structure (holding `GMap`, `ColTimeline`, `step`). <!-- id: 7 -->
    - [x] Implement `init!`, `run!`, `execute_step!`, `make_step!` (porting `sat_machine.jl`). <!-- id: 8 -->
    - [x] Implement `send_to_destine_by_origin!` and `send_to_destine!`. <!-- id: 9 -->
- [x] **Migrate GraphPow** <!-- id: 10 -->
    - [x] Create `AbsSat/GraphPow` directory. <!-- id: 11 -->
    - [x] Port `graph_pow.jl` and related logic (`filter`, `join`, `up`). <!-- id: 12 -->
    - [x] Ensure integration with `ColTimelinePow`. <!-- id: 13 -->
- [x] **Integration** <!-- id: 14 -->
    - [x] Create an integration test in `Main.lean` or a dedicated test file. <!-- id: 15 -->
    - [x] Load `test.cnf` using `ImportCnf`. <!-- id: 16 -->
    - [x] Run `SatMachine.run!` on the loaded `GMap`. <!-- id: 17 -->


- [x] **Final Verification** <!-- id: 19 -->
    - [x] **Simple Case**: Verify execution on a simple instance (`test.cnf`) ensuring correct solution finding. <!-- id: 20 -->
    - [x] **Concrete Theorems**: Prove properties for specific graph sizes (e.g., N=1, N=2) (Verified via runtime assertions in `Verification.lean`). <!-- id: 21 -->
    - [x] **General Theorems**: Proved general structural properties (step increase, stage transition) for pure components `close_vars!`, `close_gates!` in `Verification.lean`. <!-- id: 22 -->

- [x] **Formal Correctness (Generalized)** <!-- id: 23 -->
    - [x] **Pure Model**: Define a pure functional model `PureSatMachine` abstracting the IO logic. <!-- id: 24 -->
    - [x] **Problem Specification**: Define `SatProblem` and the `Solvable` predicate in Lean. <!-- id: 25 -->
    - [x] **Soundness Proof**: Prove that any solution found by `PureSatMachine` implies the SAT instance is true. <!-- id: 26 -->
    - [x] **Completeness Proof**: Prove that if `Solvable(P)`, `PureSatMachine` eventually finds a solution. <!-- id: 27 -->

- [x] **Implement Join Logic** <!-- id: 28 -->
    - [x] Implement `PathDocNode.union`. <!-- id: 29 -->
    - [x] Implement `PathColNodes.union!`. <!-- id: 30 -->
- [x] **Final Documentation & Narrative** <!-- id: 33 -->
    - [x] Create `README_VERIFICATION.md` index. <!-- id: 34 -->
    - [x] Create `verification_inseguridad_autor_main.md` narrative. <!-- id: 35 -->
