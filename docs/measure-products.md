# Product measures

`Measure.prod` denotes the unique measure satisfying the measurable rectangle
formula. Its last argument is `HasUniqueProduct μ ν`, which is supplied
automatically for sigma-finite factors, a zero factor, or a subsingleton factor
space. S-finiteness alone does not supply uniqueness.

The public import remains `Mathlib.MeasureTheory.Measure.Prod`.

| Interface | Required evidence | Meaning |
| --- | --- | --- |
| `IsProductMeasure μ ν ρ` | None | `ρ (s ×ˢ t) = μ s * ν t` for measurable `s` and `t` |
| `HasUniqueProduct μ ν` | None | Exactly one measure satisfies that formula |
| `μ.primitiveProd ν` | None | Maximal product obtained from countable rectangle covers |
| `μ.productBySections ν` | `HasMeasurableSections μ ν` | Integral of vertical section measures against `μ` |
| `μ.prod ν` | `HasUniqueProduct μ ν` | The uniquely determined product |

All these measures live on the fixed product sigma-algebra. The primitive
construction does not silently replace it with a completed measurable space.

## Construction domains

`primitiveProd` follows Fremlin's terminology (§251C and notes), restricted here
to the fixed product sigma-algebra. `productBySections` is our descriptive API
name for a product measure defined through iterated integration, not a claim
that “iterated product measure” is a standard binary-measure-theory term.
For measurable `s`, its formula is
`(μ.productBySections ν) s = ∫⁻ x, ν (Prod.mk x ⁻¹' s) ∂μ`.

`HasMeasurableSections μ ν` means that, for each measurable subset `s` of the
product, the scalar function `fun x => ν (Prod.mk x ⁻¹' s)` is almost everywhere
measurable with respect to `μ`. This is sufficient to construct the iterated
measure directly by countable additivity. An s-finite second factor supplies
this evidence; the first factor may be arbitrary.

Almost everywhere measurability of the measure-valued section family implies
this scalar condition via `HasMeasurableSections.of_aemeasurable`.
`Measure.productBySections_eq_bind` proves agreement with the Giry construction under
that stronger hypothesis. No converse between the two measurability conditions
is assumed.

The section-integral evaluation theorem `Measure.productBySections_apply` requires
the evaluated set to be measurable. The cover formula
`Measure.primitiveProd_apply` applies to every set. In that formula the covering
rectangles have measurable sides, and extended nonnegative multiplication uses
`0 * ∞ = 0`.

Uniqueness is an exact predicate, rather than a synonym for sigma-finiteness.
For example, `(Measure.dirac Unit.unit).prod ν` is available for arbitrary `ν`
because its first carrier is a singleton. Different proofs of a construction's
domain give definitionally equal results.

The coordinate projection rules let `fun_prop` handle almost everywhere
measurable coordinate functions directly on the unique-product domain.

## Comparisons and migration

`Measure.prod_eq_primitiveProd` and `Measure.prod_eq_productBySections` identify the
constructions when their respective domains are present. When using the latter
in `simp only`, supplying its operands as `Measure.prod_eq_productBySections μ ν`
lets the default evidence elaborate before simplification.

`Measure.prod_prod s t hs ht` is the rectangle law on the uniqueness domain.
For sigma-finite factors, `Measure.prod_prod_of_sigmaFinite s t` also evaluates
rectangles with arbitrary sides. Coordinatewise pushforward commutes with the
unique product only with uniqueness evidence for both the source and image
factors; sigma-finiteness of an arbitrary pushforward is not presumed.

Finite and probability measure wrappers, independence laws, and sigma-finite
product decompositions use ordinary `prod`. The general s-finite kernel,
density, and integration constructions use `productBySections`, with their broader
hypotheses preserved. The s-finite Tonelli and symmetry results belong to that
ordered construction. They do not identify it with the primitive product.

The ambient `MeasureSpace` instance on a pair retains the ordered volume
convention, with an s-finite second volume. `Measure.volume_eq_productBySections`
exposes this choice. On sigma-finite factors it agrees with ordinary `prod` by
the comparison theorem. There is no competing product-volume instance.

## Formal counterexample and checks

`Counterexamples.ProductMeasure` uses infinity-scaled Lebesgue measure on the
real line. Both factors are s-finite. The product defined by section integrals gives the diagonal
mass zero, while the primitive product gives it infinite mass. A second
explicit rectangle-law witness proves failure of `HasUniqueProduct`.

`MathlibTest.MeasureProductStrict` checks the domains of ordinary `prod` and
`productBySections`, including failure to infer uniqueness merely from
s-finiteness; it also checks local evidence, proof irrelevance, zero and
singleton cases. `MathlibTest.MeasureDerivedStrict` retains the bridge from
measure-valued measurability to the iterated construction.

The distinction between maximal products and products defined by iterated integration is discussed in
[Vákár and Ong, *On S-Finite Measures and Kernels*, Theorems 3–4](https://arxiv.org/html/1810.01837).
For the primitive product and its Carathéodory measurable space, see
[Fremlin, *Measure Theory*, §251A–E](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf).
For an independent use of Fremlin's terminology, see
[König, *Fubini–Tonelli Theorems on the Basis of Inner and Outer Premeasures*, §3](https://www.heldermann-verlag.de/jca/jca16/jca0786_b.pdf).
