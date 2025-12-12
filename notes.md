### **Possible Improvements for AlphaGeometry2**

#### **1. Missing Core Functionality**
These features are essential for a usable proof assistant but are absent in this "benchmark-only" release. These implementations should be done before any other explorations.

* **Implement Proof Traceback & Extraction**
    * **The Problem:** Currently, `ddar.py` uses "Forward Chaining" to flood the database with facts but forgets how it derived them. It outputs "Proven" but cannot explain *why*.
    * **The Task:** Modify `DDAR` classes to store a **Dependency Graph**.
        * Create a `Fact` class (wrapping `FormalLine`, `FormalAngle`, etc.) that stores `parents` (list of facts used to derive it) and `rule_name` (e.g., "similar_triangles").
        * Update `elimination.py`: When Gaussian elimination combines rows, record which rows were combined.
        * **Goal:** Implement a `get_proof_trace(goal)` function that back-propagates from the goal to the axioms to generate a human-readable proof tree.

* **Natural Language Proof Generation**
    * **The Task:** Once we have the proof trace (from the step above), use a simple template-based system or a small LLM to translate the symbolic steps into natural text.
    * **Example:** Convert `perp(a,b,c,d) & perp(c,d,e,f) -> para(a,b,e,f)` into *"Since AB is perpendicular to CD and CD is perpendicular to EF, AB is parallel to EF."*

#### **2. Functional Enhancements (Logic & Domains)**
Expand the mathematical universe the system can reason about.

* **Integrate the "Area Method" (Area Table)**
    * **The Problem:** The current system reasons about Angles (`ElimAngle`), Length Ratios (`ElimDistMul`), and Linear Distances (`ElimDistAdd`). It lacks explicit reasoning for **Signed Areas** ($S_{ABC}$), which is a powerful tool for Olympiad geometry (the "Area Method").
    * **The Task:**
        * Add a new class `ElimArea` in `elimination.py`.
        * Add rules in `ddar.py` to handle area properties (e.g., "If $M$ is the midpoint of $BC$, then $S_{ABM} = S_{ACM}$").
        * Connect `ElimArea` to `ElimDistMul` (e.g., ratio of areas = ratio of bases * ratio of heights).

* **Complex Number Engine**
    * **The Task:** Implement a parallel engine that verifies properties using Complex Numbers coordinates instead of Cartesian coordinates in `numericals.py`. This is often more robust for rotation-heavy problems and provides an alternative "truth check" for the symbolic engine.

* **Inequality Reasoning**
    * **The Problem:** DDAR currently handles equalities (`==`). It cannot handle inequalities (e.g., $AB + BC > AC$ or "Point $P$ is inside Triangle $ABC$").
    * **The Task:** Extend `elimination.py` to handle linear inequalities (Simplex method or similar) to solve problems involving bounds or convexity.

#### **3. Exploration & AI Research (Advanced)**
Use this codebase as a gym for training agents, leveraging your interest in RL and Neuro-symbolic systems.

* **Reinforcement Learning for Auxiliary Points**
    * **The Idea:** Currently, `test.py` uses *hardcoded* auxiliary points. The original paper used a massive Gemini model. We can try to solve this with RL.
    * **The Project:**
        * **State:** The graph of known facts in `DDAR`.
        * **Action:** Construct a point (e.g., "Midpoint of AB", "Intersection of line L and Circle C").
        * **Reward:** +1 if the new point leads to a proof (rank of the `ElimCore` matrix increases or goal is reached), -0.1 per step (time penalty).
        * **Goal:** Train a smaller, specialized agent (like PPO or DQN) to propose useful points without needing a generic LLM.

* **Fine-tuning a "Small" LLM (Llama-3-8B / Gemma-2)**
    * **The Task:** The original AlphaGeometry used a massive model trained on 100M synthetic proofs.
    * **Experiment:** Can we fine-tune a consumer-grade LLM (e.g., 8B parameters) to suggest auxiliary points?
    * **Pipeline:** Use `DDAR` to generate thousands of random solvable theorems (synthetic data generation), then fine-tune a local model on this data to predict the next construction step.

* **Symbolic Engine Optimization (C++ Port)**
    * **The Task:** The README notes that DeepMind's internal version uses C++ for speed (300x faster).
    * **Project:** Re-implement `elimination.py` and `ddar.py` in **Rust** or **C++** and bind it to Python using PyBind11. This would allow you to run massive searches (e.g., trying 1000 auxiliary point guesses per second) that are currently impossible in Python.

#### **4. Bug Fixes & Code Quality**
Low-hanging fruit to improve stability.

* **Numerical Precision Stability**
    * **The Issue:** `numericals.py` uses `ATOM = 1e-12`. In complex constructions, floating-point errors accumulate.
    * **The Fix:** Implement an adaptive precision mechanism or replace `numpy` floats with arbitrary-precision decimal types (`decimal` module) or `gmpy2` for the ground-truth verification step.

* **Degenerate Case Handling**
    * **The Issue:** The system might fail if a construction collapses (e.g., "Intersection of two identical lines").
    * **The Fix:** Systematically fuzz-test the `ddar.py` engine with degenerate inputs (points on top of each other, zero-radius circles) and ensure it throws informative errors or handles them gracefully instead of crashing the matrix solver.

* **Double Point Robustness**
    * **The Task:** Verify if `merge_points` in `ddar.py` correctly handles *transitive* equality (If $A=B$ and $B=C$, does it instantly know $A=C$ in all contexts?). Create test cases specifically designed to break the current merging logic.