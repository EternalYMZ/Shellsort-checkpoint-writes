import Shellsort.CheckpointChange

namespace Shellsort.PhysicalSlotWrites

/-- One operation overwrites one physical slot with one complete record. -/
def execute {n : ℕ} {α : Type*} (initial : Fin n → α) :
    List (Fin n × α) → (Fin n → α)
  | [] => initial
  | (i,x) :: tail => execute (Function.update initial i x) tail

private theorem untouched {n : ℕ} {α : Type*} (writes : List (Fin n × α))
    (initial : Fin n → α) (i : Fin n) (absent : i ∉ writes.map Prod.fst) :
    execute initial writes i = initial i := by
  induction writes generalizing initial with
  | nil => rfl
  | cons w ws ih =>
    rcases w with ⟨j,x⟩
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    rw [execute, ih _ absent.2, Function.update_of_ne absent.1]

theorem any_trace_lower {n : ℕ} (p q : RankPlacement n)
    (writes : List (Fin n × Fin n)) (reaches : execute p.symm writes = q.symm) :
    checkpointChange p q ≤ writes.length := by
  rw [checkpointChange_eq_slots]
  unfold checkpointSlotChange
  have sub : (Finset.univ.filter (fun i => p.symm i ≠ q.symm i)) ⊆
      (writes.map Prod.fst).toFinset := by
    intro i hi
    by_contra missing
    have h := untouched writes p.symm i (by simpa using missing)
    rw [reaches] at h
    exact (Finset.mem_filter.mp hi).2 h.symm
  exact (Finset.card_le_card sub).trans (by simpa using (writes.map Prod.fst).toFinset_card_le)

private theorem write_targets {n : ℕ} {α : Type*} (initial target : Fin n → α)
    (slots : List (Fin n)) (i : Fin n) :
    execute initial (slots.map (fun j => (j, target j))) i =
      if i ∈ slots then target i else initial i := by
  induction slots generalizing initial with
  | nil => simp [execute]
  | cons j js ih =>
    simp only [List.map_cons, execute, ih, List.mem_cons]
    by_cases h : i = j
    · subst j; simp
    · simp [h, Function.update_of_ne]

/-- If target records are available for copying, write each changed slot
exactly once. This counts main-array writes, with target lookup uncharged. -/
theorem attainable {n : ℕ} (p q : RankPlacement n) :
    ∃ writes : List (Fin n × Fin n), execute p.symm writes = q.symm ∧
      writes.length = checkpointChange p q := by
  let changed := Finset.univ.filter (fun i => p.symm i ≠ q.symm i)
  refine ⟨changed.toList.map (fun j => (j,q.symm j)), ?_, ?_⟩
  · funext i
    rw [write_targets]
    by_cases h : p.symm i = q.symm i <;> simp [changed,h]
  · simp [changed,checkpointChange_eq_slots,checkpointSlotChange]

/-- The end of each segment is the start of the following segment. -/
inductive Visits {n : ℕ} : RankPlacement n → List (RankPlacement n) →
    List (List (Fin n × Fin n)) → Prop where
  | done (p) : Visits p [] []
  | next {p q rest w ws} (reaches : execute p.symm w = q.symm)
      (later : Visits q rest ws) : Visits p (q :: rest) (w :: ws)

def routeCost {n : ℕ} (p : RankPlacement n) : List (RankPlacement n) → ℕ
  | [] => 0
  | q :: rest => checkpointChange p q + routeCost q rest

theorem visits_lower {n : ℕ} {p : RankPlacement n} {points writes}
    (h : Visits p points writes) :
    routeCost p points ≤ (writes.map List.length).sum := by
  induction h with
  | done => simp [routeCost]
  | next reaches _ ih =>
    simpa [routeCost] using Nat.add_le_add (any_trace_lower _ _ _ reaches) ih

theorem visits_attainable {n : ℕ} (p : RankPlacement n)
    (points : List (RankPlacement n)) :
    ∃ writes, Visits p points writes ∧ (writes.map List.length).sum = routeCost p points := by
  induction points generalizing p with
  | nil => exact ⟨[],Visits.done p,rfl⟩
  | cons q rest ih =>
    obtain ⟨w,hw,hl⟩ := attainable p q
    obtain ⟨ws,hs,hc⟩ := ih q
    exact ⟨w :: ws, Visits.next hw hs, by simp [routeCost,hl,hc]⟩

end Shellsort.PhysicalSlotWrites
