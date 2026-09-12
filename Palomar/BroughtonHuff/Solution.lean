import BroughtonHuff

open scoped MeasureTheory

theorem BroughtonHuff.exists_measurableSet_iSup_not_measurableSet_of_strictMono
    {α : Type*} {𝓐 : ℕ → MeasurableSpace α} (hm : StrictMono 𝓐) :
    ∃ s, MeasurableSet[⨆ n, 𝓐 n] s ∧ ∀ n, ¬MeasurableSet[𝓐 n] s := by
  exact proof_exists_measurableSet_iSup_not_measurableSet_of_strictMono hm

theorem BroughtonHuff.not_exists_measurableSpace_iUnion_of_strictMono
    {α : Type*} {𝓐 : ℕ → MeasurableSpace α} (hm : StrictMono 𝓐) :
    ¬ ∃ 𝓐' : MeasurableSpace α,
      ∀ s, MeasurableSet[𝓐'] s ↔ ∃ n, MeasurableSet[𝓐 n] s := by
  exact proof_not_exists_measurableSpace_iUnion_of_strictMono hm
