import Mathlib.MeasureTheory.Integral.Prod

namespace MeasureTheory

theorem StronglyMeasurable.prod_swap {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [TopologicalSpace γ]
    {f : β × α → γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.swap) :=
  hf.comp_measurable measurable_swap

theorem StronglyMeasurable.fst {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [TopologicalSpace γ]
    {f : α → γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.1) :=
  hf.comp_measurable measurable_fst

theorem StronglyMeasurable.snd {α β γ : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [TopologicalSpace γ]
    {f : β → γ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun z : α × β => f z.2) :=
  hf.comp_measurable measurable_snd

end MeasureTheory
