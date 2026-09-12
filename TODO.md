# Mathematical fidelity and API hygiene backlog

This file records public mathematical interfaces that should be audited or migrated under the
strict-domain, representation, public-notation, and function-presentation policies in
`FORK_DESIGN.md`.  It is an
implementation backlog, not a claim that Lean is unsound and not a claim that every total
implementation or custom notation is defective.  A documented fallback is still non-strict when
the ordinary public operation erases its mathematical domain.  An explicitly named/default-taking
extension is not a *silent-totalization* defect, but that fact alone does not make it
mathematician-facing: it can still be the wrong primary interface if papers would instead state a
domain condition, work on a constrained object, or pass to an a.e.-equivalence class.  An
unreachable implementation fallback is acceptable only when the public boundary proves it
unreachable and exposes the actual mathematical object.

The list is sorted by estimated effort for a coherent migration, from smallest to largest.  Only the
bucket order is asserted; entries within one bucket are not finely ranked without a dependency
prototype.  Effort does not measure mathematical importance:

- **S**: a bounded declaration or theorem family with an existing strict substrate; normally a few
  files.
- **M**: one coherent subsystem, with statement and consumer migration or a local design decision.
- **L**: a cross-module API with notation, instances, or many downstream consumers; stage the work.
- **XL**: foundational hierarchy or ubiquitous notation; prototype first and migrate in slices.

For every strict-partiality migration in the S--XL sections below:

1. expose definedness through an input type, proof argument, or explicit partiality;
2. give any retained total extension a name that identifies its fallback;
3. audit theorem statements that currently succeed on the invalid-domain branch;
4. preserve a proved bridge on the valid domain and record interface strictness separately from
   implementation strictness;
5. add negative tests showing that strict code cannot recover the old fallback, including after
   simplification; and
6. run targeted builds plus the affected downstream tests at the final source state.

## S -- bounded corrections and strict facades

- [x] **Correct the stale `Measure.map` module overview.**
  The overview now describes pushforward only along an a.e.-measurable map and no longer documents
  an invalid-domain fallback.

- [ ] **Require parabolicity for `GeneralLinearGroup.parabolicEigenvalue`.**
  `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/FinTwo.lean:103` exposes `trace / 2` as an
  eigenvalue for every matrix although the docstring calls the nonparabolic case junk.  Make the
  eigenvalue operation take `m.IsParabolic`; retain half-trace under its own total name.

- [ ] **Make real-valued Dirichlet density conditional on existence.**
  `Mathlib/NumberTheory/NumberField/DirichletDensity.lean:90` defines
  `NumberField.Set.dirichletDensity` as zero when no density exists.  Use
  `HasDirichletDensity` at the ordinary boundary and explicitly name any zero-default projection.

- [ ] **Restrict number-field heights to algebraic inputs and fix their documentation.**
  `absMulHeight₁` and `absLogHeight₁` in
  `Mathlib/NumberTheory/Height/NumberField.lean:137` and `:146` map a nonalgebraic element to
  multiplicative height one and logarithmic height zero.  Require `IsIntegral ℚ x` (or an
  algebraic-number carrier); also correct the multiplicative docstring, which currently says its
  fallback is zero.

- [ ] **Remove the pole-only branch from `riemannZeta_ne_zero_of_one_le_re`.**
  `Mathlib/NumberTheory/LSeries/Nonvanishing.lean:413` omits `s ≠ 1` because the chosen value at
  the pole happens to be nonzero.  State the mathematical theorem away from the pole; treat a strict
  zeta/L-series evaluation separately under the L backlog.

- [ ] **Put `ArchimedeanClass.stdPart` on finite elements.**
  `Mathlib/Algebra/Order/Ring/StandardPart.lean:273` maps infinite inputs to zero, conflating them
  with infinitesimals in results such as `stdPart_eq_zero`.  Use the existing `FiniteElement K`
  domain and retain any ambient zero extension under an explicit name.

- [ ] **Require `1 < q` for `ArithmeticFunction.ofPowerSeries`.**
  `Mathlib/NumberTheory/ArithmeticFunction/LFunction.lean:66` uses the constant coefficient when
  `q ≤ 1`; algebra-hom laws intentionally exploit that branch.  Put the injective-power
  hypothesis in the constructor and name any constant-coefficient extension explicitly.

- [ ] **Give `Nat.maxPrimeFac` its actual domain.**
  `Mathlib/Data/Nat/MaxPrimeFac.lean:39` returns zero at zero and one at one, neither of which is a
  greatest prime divisor.  Require `1 < n` or return explicit failure.

- [ ] **Require nonzero mass for `FiniteMeasure.normalize`.**
  `FiniteMeasure.normalize` in
  `Mathlib/MeasureTheory/Measure/ProbabilityMeasure.lean:468` returns an arbitrary Dirac probability
  measure when the input measure has mass zero.  Put `μ ≠ 0` at the ordinary normalization boundary;
  retain any arbitrary-Dirac extension under an explicit name.

- [ ] **Require primitivity for `DirichletCharacter.rootNumber`.**
  `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean:272` exposes the primitive-character
  Gauss-sum formula for every character and documents the nonprimitive result as junk.  Require
  `IsPrimitive χ` for the ordinary root number, or name the unrestricted expression as a formula.
  Do not conflate it with the separate root number obtained from an induced primitive character.

## M -- subsystem migrations

- [ ] **Make finite multiplicity a checked projection.**
  `Mathlib/RingTheory/Multiplicity.lean:47` defines `multiplicity` as
  `(emultiplicity a b).toNat`, so infinite multiplicity becomes zero.  Keep `emultiplicity` as the
  faithful invariant and require `FiniteMultiplicity` for a natural-valued projection.  Migrate
  derived natural-valued consumers such as `padicValNat`, identified with `multiplicity` in
  `Mathlib/NumberTheory/Padics/PadicVal/Defs.lean:49`; in particular,
  `padicValNat_zero_right` in `Mathlib/Data/Nat/MaxPowDiv.lean:106` is the same infinite-to-zero case.

- [ ] **Require monicity for polynomial division-by-monic notation.**
  `Polynomial.divByMonic` and `Polynomial.modByMonic` in
  `Mathlib/Algebra/Polynomial/Div.lean:132` and `:137` accept a nonmonic divisor and return quotient
  zero and the original dividend.  Thread `q.Monic` through `/ₘ` and `%ₘ`, reusing
  `divModByMonicAux`.

- [ ] **Exclude the zero polynomial from finite root multisets and multiplicities.**
  `Polynomial.roots` in `Mathlib/Algebra/Polynomial/Roots.lean:58` gives the empty multiset at zero
  (line 71), while `Polynomial.rootMultiplicity` in
  `Mathlib/Algebra/Polynomial/Div.lean:498` returns zero even though a largest dividing power does
  not exist.  Require `p ≠ 0` for finite root multisets and finite multiplicities, retaining infinity
  where appropriate.  Ordinary set-valued root loci may remain defined for arbitrary polynomials.

- [ ] **Make scheme order of vanishing carry its point and function domains.**
  `AlgebraicGeometry.Scheme.ord` in `Mathlib/AlgebraicGeometry/OrderOfVanishing.lean:52` returns
  zero for the zero rational function and for points not of codimension one.  Reuse `ordHom` for the
  point condition and expose nonzeroness or an infinity-preserving codomain.

- [ ] **Unify strict nilpotency invariants.**
  `Mathlib/RingTheory/Nilpotent/Defs.lean:78`, `Mathlib/GroupTheory/Nilpotent.lean:530`, and
  `Mathlib/Algebra/Lie/Nilpotent.lean:389` assign zero to nonnilpotent objects; `IsNilpotent.exp` and
  `LieModule.lowerCentralSeriesLast` inherit misleading values.  Require nilpotency evidence or use
  an extended natural invariant, then migrate the element, group, and Lie families coherently.

- [ ] **Require injectivity for `LinearMap.leftInverse`.**
  `Mathlib/LinearAlgebra/Basis/VectorSpace.lean:266` returns the zero map for a noninjective linear
  map.  Make the constructor consume injectivity (or splitting data) and explicitly name any
  zero-default extension.

- [ ] **Bundle admissible root pairs for root-chain data.**
  `RootPairing.chainTopCoeff`, `chainBotCoeff`, `chainTopIdx`, and `chainBotIdx` in
  `Mathlib/LinearAlgebra/RootSystem/Chain.lean:110`, `:120`, `:366`, and `:377` return zero or the
  input index when the two roots are not linearly independent.  Take the independence proof once in
  a bundled admissible pair.

- [ ] **Require `ExcenterExists` for excenter geometry.**
  `Affine.Simplex.exsphere`, `excenter`, and `exradius` in
  `Mathlib/Geometry/Euclidean/Incenter.lean:346`, `:368`, and `:413` fabricate an arbitrary point
  and a zero-radius sphere when the excenter does not exist.  Put the existing validity predicate in
  the three public operations.

- [ ] **Make Newton iteration preserve derivative invertibility.**
  `Polynomial.newtonMap` in `Mathlib/Dynamics/Newton.lean:44` returns its input when the derivative
  value is not a unit, creating spurious fixed points.  Require unit evidence for a step and design
  iteration around propagation or explicit failure; keep the identity extension under its own name.

- [ ] **Put periods and periodic orbits on periodic points.**
  `Function.minimalPeriod` and `Function.periodicOrbit` in
  `Mathlib/Dynamics/PeriodicPts/Defs.lean:245` and `:401` return zero and the empty cycle for a
  nonperiodic point.  Use a periodic-point input for ordinary period/orbit names; migrate the
  inherited `MulAction.period` convention too.

- [ ] **Use extended graph distance and girth until finiteness is proved.**
  `SimpleGraph.dist` in `Mathlib/Combinatorics/SimpleGraph/Metric.lean:206` maps unreachable pairs
  to zero, while `SimpleGraph.girth` in `Mathlib/Combinatorics/SimpleGraph/Girth.lean:115` maps an
  acyclic graph's infinite girth to zero.  Keep `edist`/`egirth` globally and require reachability or
  a cycle for natural-valued projections.

- [ ] **Replace the unbounded fallback in `SimpleGraph.cliqueNum`.**
  `Mathlib/Combinatorics/SimpleGraph/Clique.lean:726` takes a natural `sSup` without boundedness, so
  graphs with arbitrarily large finite cliques inherit the conditional-supremum junk value.  Choose
  and document an extended finite-clique invariant before exposing a checked natural projection.

- [ ] **Require `n ≠ 1` for `Nat.minFac`.**
  `Mathlib/Data/Nat/Prime/Defs.lean:218` returns one at one, although one has no prime factor.  Do not
  exclude zero: `minFac_zero` correctly identifies its least prime divisor as two.

- [ ] **Give `Nat.log` and `Nat.clog` their extremal domains.**
  `Mathlib/Data/Nat/Log.lean:62` and `:335` accept bases at most one and other inputs for which the
  advertised largest/least exponent characterization fails.  Encode the precise base and argument
  conditions; preserve any computational defaults under explicit names.

- [ ] **Make `Nat.findGreatest` report absence.**
  `Mathlib/Data/Nat/Find.lean:165` returns zero when no bounded witness satisfies the predicate.
  Require existence, return `Option ℕ`, or rename the defaulting search.

- [ ] **Require eventual constancy for monotone-sequence limits.**
  `monotonicSequenceLimitIndex` and `monotonicSequenceLimit` in
  `Mathlib/Order/OrderIsoNat.lean:273` and `:278` assign a junk index/value to a monotone sequence
  that never stabilizes.  Take eventual constancy, with well-foundedness used only to synthesize it.

- [ ] **Put fundamental circuits and cocircuits on their admissible data.**
  `Matroid.fundCircuit` and `Matroid.fundCocircuit` in
  `Mathlib/Combinatorics/Matroid/Circuit.lean:211` and `:690` accept inadmissible data and then need
  not return circuits/cocircuits; documented invalid cases return singleton or inserted sets.  Bundle
  the independence, closure, base, and membership hypotheses already repeated by their valid-case
  theorem families.

- [ ] **Put bundle coordinate changes on chart overlaps.**
  `Bundle.Trivialization.coordChange` in
  `Mathlib/Topology/FiberBundle/Trivialization.lean:754` accepts every base point even though its
  identity, composition, and continuity theorems require membership in the relevant base sets; the
  proof-carrying `coordChangeHomeomorph` at line 795 is the existing strict substrate.  The analogous
  `coordChangeL` in `Mathlib/Topology/VectorBundle/Basic.lean:266` returns the identity outside the
  overlap.  Make the ordinary coordinate-change operations take overlap evidence or a point in the
  overlap, and keep total representatives only under names that identify their implementation role.
  Preserve technical local-map representatives such as trivialization inverses when all exported
  statements prove that their values outside the base set are irrelevant.

- [ ] **Make conditional probability require a normalizable event.**
  `ProbabilityTheory.cond` in `Mathlib/Probability/ConditionalProbability.lean:76` exposes
  `(μ s)⁻¹ • μ.restrict s` as `μ[· | s]` for every set.  Require measurability and
  `0 < μ s < ∞`, or explicitly identify the normalization extension.

- [ ] **Replace integration-facing `ContinuousMap.mkD` with an a.e.-continuous-family interface.**
  `ContinuousMap.mkD` in `Mathlib/Topology/ContinuousMap/Basic.lean:320` honestly takes an explicit
  fallback, so it is not a silent totalization; nevertheless it interprets every bare function as a
  continuous map by replacing a noncontinuous function wholesale.  The integration guide in
  `Mathlib/MeasureTheory/SpecificCodomains/ContinuousMap.lean:40` recommends this spelling even when
  every family member is continuous, chiefly to avoid dependent types.  Model the paper-level claim
  instead: an a.e.-continuous family determines an a.e.-class of `C(Y, E)`-valued maps, independent
  of the representative on the null set.  Carry a.e. continuity at that boundary and separately
  require the strong measurability and integrability used downstream; quotienting alone does not
  prove them.  Keep `mkD` only as an explicitly technical representative constructor if still needed
  behind that boundary.

- [ ] **Prevent impossible regularity requests from becoming zero operators.**
  `TestFunction.fderivCLM`, `lineDerivCLM`, and supported-map derivatives in
  `Mathlib/Analysis/Distribution/TestFunction.lean:510`, `:564` and
  `Mathlib/Analysis/Distribution/ContDiffMapSupportedIn.lean:379` return zero when the requested
  regularity inequality fails.  Put the inequality in the constructor and automate its proof.

- [ ] **Require a dense domain for `LinearPMap.adjoint`.**
  `Mathlib/Analysis/InnerProductSpace/LinearPMap.lean:152` returns a partial operator, but its
  `toFun` is zero when the original domain is not dense.  The output partiality does not encode this
  missing construction hypothesis; use dense-domain evidence or the adjoint relation.

- [ ] **Require uniform continuity for `CauchyFilter.extend`.**
  `Mathlib/Topology/UniformSpace/Completion.lean:224` evaluates at an arbitrarily selected point
  when the function is not uniformly continuous.  Make uniform continuity part of the extension
  input and name any arbitrary extension explicitly.

- [ ] **Make vector-measure products and densities conditional constructions.**
  `VectorMeasure.prod` in `Mathlib/MeasureTheory/VectorMeasure/Prod.lean:52` chooses zero when no
  product exists, and `VectorMeasure.withDensity` in
  `Mathlib/MeasureTheory/VectorMeasure/WithDensityVec.lean:42` uses zero when integrability fails.
  Require `HasProd`/integrability at the ordinary boundary.

- [ ] **Define the intended domain of generalized `InformationTheory.klDiv`.**
  `Mathlib/InformationTheory/KullbackLeibler/Basic.lean:57` accepts arbitrary measures although its
  mass correction is justified for finite measures; for example, zero against an infinite-mass
  measure collapses to zero through `ν.real univ`.  Either restrict the public divergence to finite
  measures or specify and verify a genuine infinite-measure extension before migrating theorems.

- [ ] **Make `LinearMap.index` carry Fredholm-style finiteness.**
  `Mathlib/Algebra/Module/LinearMap/Index.lean:40` subtracts natural `finrank`s of kernel and
  cokernel without finite-rank hypotheses.  State the appropriate finiteness assumptions and audit
  the intended general-ring scope.

- [ ] **Give Euler characteristic both required finiteness conditions.**
  `GradedObject.eulerChar` and its complex wrapper in
  `Mathlib/Algebra/Homology/EulerCharacteristic.lean:118` inherit zero from `finsum` on infinite
  support and from `finrank` on infinite-dimensional terms.  Require finite-dimensional relevant
  objects and finite actual support; coordinate with the XL `finrank` migration and the separate
  `finsum` classification audit.

- [ ] **Require a finite residue field for elliptic local factors.**
  `WeierstrassCurve.localPolynomial` in
  `Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean:43` permits an infinite residue field;
  `Nat.card` then makes its field size and point count zero.  Propagate finite-residue-field evidence
  through local power series and Euler factors.

- [ ] **Make analytic and meromorphic orders domain-bearing.**
  `analyticOrderAt`/`analyticOrderNatAt` in `Mathlib/Analysis/Analytic/Order.lean:47` and `:61`, and
  `meromorphicOrderAt` in `Mathlib/Analysis/Meromorphic/Order.lean:50`, return zero outside their
  analytic/meromorphic domains; the natural analytic order also collapses genuine infinite order.
  Require the germ hypothesis and retain infinity until finite order is proved.

## L -- staged cross-module migrations

- [ ] **Put matroid closure on subsets of the ground set.**
  `Matroid.closure` in `Mathlib/Combinatorics/Matroid/Closure.lean:135` deliberately extends closure
  to every `Set α` by replacing `X` with `X ∩ M.E`; the module describes off-ground inputs as junk,
  and the resulting operation is not extensive on all `Set α`.  Reuse `Matroid.subtypeClosure` at
  line 116 to make the ordinary closure domain-bearing, or prototype an equally strict proof-last
  interface.  Retain the intersection convention only under an explicit extension name if real
  consumers still require it.  The current surface has roughly 258 `M.closure` matching lines across
  nine maintained files, so migrate the closure theorem family and its rank, minor, circuit, and loop
  consumers as one staged change.

- [ ] **Require integrality for `minpoly`.**
  `Mathlib/FieldTheory/Minpoly/Basic.lean:41` assigns polynomial zero to a nonintegral element;
  `minpoly.aeval` at line 89 then states unconditionally that every element is a root of its minimal
  polynomial.  Put `IsIntegral` in the ordinary construction and theorem family; keep an explicitly
  named zero extension only as a bridge.

- [ ] **Replace finite separable/inseparable degree projections outside their domains.**
  `Field.finSepDegree` in `Mathlib/FieldTheory/SeparableDegree.lean:141` uses `Nat.card` even for a
  nonalgebraic extension, and `Field.finInsepDegree` in
  `Mathlib/FieldTheory/SeparableClosure.lean:281` inherits `finrank`'s infinite-to-zero behavior.
  Require the correct algebraicity/finite-degree evidence or expose cardinal-valued invariants.

- [ ] **Make rational-function evaluation reject poles.**
  `RatFunc.eval` in `Mathlib/FieldTheory/RatFunc/AsPolynomial.lean:143` evaluates a pole to zero and
  consequently fails ring laws there.  Require regularity/denominator nonzeroness at the point, while
  respecting reduced-rational-function rather than source-expression semantics.

- [ ] **Put finite factorization data on nonzero inputs.**
  `Nat.factorization` in `Mathlib/Data/Nat/Factorization/Defs.lean:50` gives zero multiplicities at
  zero, and `Nat.primeFactors` in `Mathlib/Data/Nat/PrimeFin.lean:37` gives the empty set although
  every prime divides zero.  The generic `factorization` and `normalizedFactors` in
  `Mathlib/RingTheory/UniqueFactorizationDomain/Finsupp.lean:32` and
  `Mathlib/RingTheory/UniqueFactorizationDomain/NormalizedFactors.lean:35` likewise return empty data
  at zero.  Use a nonzero carrier or explicit failure for finite lists/counts; keep units admissible
  with empty factorization.  `Associates.factors` already supplies a faithful extended precedent by
  returning `⊤` at zero (`Mathlib/RingTheory/UniqueFactorizationDomain/FactorSet.lean:223`).

- [ ] **Migrate natural cardinalities away from infinity-to-zero.**
  `Nat.card` in `Mathlib/SetTheory/Cardinal/Finite.lean:41` and `Set.ncard` in
  `Mathlib/Data/Set/Card.lean:613` return zero on infinite inputs.  Require `Finite α`/`s.Finite` for
  natural values and use `ENat.card`/`Set.encard` globally.

- [ ] **Make lossy extended-value conversions checked or explicitly defaulted.**
  `ENat.toNat` (`Mathlib/Data/ENat/Basic.lean:118`), `Cardinal.toNat`
  (`Mathlib/SetTheory/Cardinal/ToNat.lean:31`), and `ENNReal.toNNReal`/`toReal`
  (`Mathlib/Basic/ENNReal/Basic.lean:225`) send infinity to zero.  Provide proof-bearing finite
  conversions and reserve `...OrZero`-style names for the current maps.

- [ ] **Separate chosen preimages from true inverses and true extensions.**
  `Function.invFun` in `Mathlib/Logic/Function/Basic.lean:526` picks an arbitrary element outside
  the range and a chosen preimage for noninjective maps.  Use equivalences/bijections for inverse
  functions and a range-indexed chosen-preimage operation for the weaker construction.
  `Function.extend` in the same file at line 835 explicitly takes an outside-range fallback, which is
  legitimate, but without `g.FactorsThrough f` it chooses one representative's `g`-value for a
  fiber and cannot agree with every original `g`-value on that fiber.  Require `FactorsThrough` for
  the ordinary extension name; keep an unrestricted chosen-representative construction under a
  descriptive name.

- [ ] **Make subgroup indices finite only with evidence.**
  `Subgroup.index` and `Subgroup.relIndex` in `Mathlib/GroupTheory/Index.lean:57` and `:64` return
  zero for infinite index.  Keep a cardinal/extended index globally and require finite index for the
  natural projection.

- [ ] **Require prime and finite local data for ramification and inertia degrees.**
  `Ideal.ramificationIdx` and `Ideal.inertiaDeg` in
  `Mathlib/RingTheory/RamificationInertia/Ramification.lean:52` and
  `Mathlib/RingTheory/RamificationInertia/Inertia.lean:44` return zero for nonprime ideals and also
  collapse infinite length/rank.  Carry primality plus the appropriate finiteness evidence, or keep
  an extended-valued invariant.

- [ ] **Put affine combinations on affine weights.**
  `Finset.affineCombination` in `Mathlib/LinearAlgebra/AffineSpace/Combination.lean:348` accepts
  arbitrary weights and chooses a base point; only weights summing to one give the intrinsic affine
  combination.  Use the affine-weight hyperplane (or a sum-one proof) and explicitly name a
  basepoint-dependent extension.

- [ ] **Require invertible derivatives for vector-field pullback and regularity for Lie brackets.**
  `VectorField.mpullbackWithin`/`mpullback` in
  `Mathlib/Geometry/Manifold/VectorField/Pullback.lean:100` and `:107` return zero when the derivative
  is noninvertible.  `mlieBracketWithin`/`mlieBracket` in
  `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean:63` and `:73` accept fields without the
  differentiability needed by the mathematical bracket.  Redesign around local diffeomorphisms and
  differentiable vector-field objects.

- [ ] **Audit and strictify local-frame/trivialization evaluation at its public boundary.**
  `IsLocalFrameOn.coeff` in
  `Mathlib/Geometry/Manifold/VectorBundle/LocalFrame.lean:186` returns zero outside the frame's set;
  pretrivializations/trivializations in `Mathlib/Topology/FiberBundle/Trivialization.lean:69` also
  expose chosen ambient values.  Preserve globally defined implementation representatives where
  useful, but require base-set membership for ordinary coordinate/evaluation names.

- [ ] **Replace arbitrary `Filter.lim` values with existence-certified limits.**
  `Filter.lim` and `Filter.limUnder` in `Mathlib/Topology/Defs/Filter.lean:255` and `:260` use
  `Classical.epsilon` and choose an arbitrary point when no limit exists.  Existence must be explicit;
  uniqueness claims additionally need the appropriate separation and nontrivial-filter conditions.
  Migrate `IsDenseInducing.extend`/`extendFrom` consumers with the same boundary discipline.

- [x] **Make measure pushforward require a.e. measurability.**
  `Measure.map` now takes a proof of a.e. measurability, normally synthesized by `fun_prop`, and
  `Measure.mapₗ` likewise requires measurability.  The arbitrary-Dirac and zero fallbacks were
  removed rather than retained under ordinary mathematical names.  The migration covers the
  existing ecosystem together with `Measure.bind`, `Measure.prod`, `FiniteMeasure.map`,
  `ProbabilityMeasure.map`, conditional-law APIs, and kernel map wrappers.  Negative tests ensure
  arbitrary functions cannot recover the former behavior, while proof-indexed congruence,
  measurable-set-first `map_apply`, and a.e.-measurable `map_map` preserve routine ergonomics.

- [x] **Separate unique product measures from iterated and primitive constructions.**
  `IsProductMeasure` records the measurable rectangle law; ordinary `Measure.prod` requires
  `HasUniqueProduct`. Sigma-finite, zero, and singleton cases supply routine evidence.
  `Measure.primitiveProd` constructs the maximal product for arbitrary factors, while
  `Measure.productBySections` uses scalar section measurability and retains the s-finite Tonelli theory.
  Finite/probability interfaces use the unique product, and genuinely s-finite consumers select
  the iterated construction explicitly. The formal infinity-scaled Lebesgue counterexample
  separates the constructions and disproves uniqueness from s-finiteness alone.

- [ ] **Make `NormedSpace.exp` require its algebra and convergence context.**
  `Mathlib/Analysis/Normed/Algebra/Exponential.lean:127` returns one if no `Algebra ℚ 𝔸`
  exists and otherwise delegates to a power-series sum without encoding summability in the
  operation.  Require the scalar-algebra data and the analytic conditions actually used.

- [ ] **Make ordinary L-series evaluation conditional on summability.**
  `LSeries` in `Mathlib/NumberTheory/LSeries/Basic.lean:164` inherits zero for nonsummable series
  from `tsum`.  Use `LSeriesHasSum`/`LSeriesSummable` at the public evaluation boundary and audit
  specializations, including zeta at its pole.

- [ ] **Strictify the separate box-integral ecosystem.**
  `BoxIntegral.integral` in `Mathlib/Analysis/BoxIntegral/Basic.lean:176` returns zero for a
  nonintegrable function.  Make integrability for the chosen integration parameters part of the
  ordinary operation.

- [ ] **Separate finite `lpNorm`/variance from extended or nonexistent values.**
  `MeasureTheory.lpNorm` in `Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean:142` maps
  non-a.e.-strongly-measurable or infinite-norm functions to zero.  `ProbabilityTheory.variance` in
  `Mathlib/Probability/Moments/Variance.lean:64` maps infinite variance to zero and centers through
  totalized expectation.  Use `MemLp`/moment hypotheses for finite values and design extended values
  without a junk mean.

- [ ] **Make conditional expectations carry their measure-theoretic hypotheses.**
  `condExp` in `Mathlib/MeasureTheory/Function/ConditionalExpectation/Basic.lean:102` and
  `condLExp` in `Mathlib/MeasureTheory/Function/ConditionalLExpectation.lean:73` return zero when the
  sigma algebra is not subordinate or the restricted measure is not sigma-finite; `condExp`
  additionally returns zero when integrability fails.  Preserve `condLExp`'s genuine extended
  nonnegative values, bundle the sigma-algebra/measure evidence, and require integrability only for
  the finite Bochner-valued construction.

- [x] **Require measurable random variables for conditional distributions.**
  `ProbabilityTheory.condDistrib` now requires joint a.e. measurability of `fun a ↦ (X a, Y a)`,
  normally synthesized by `fun_prop`, while retaining the normal freedom to choose versions on null
  conditioning fibres.

- [x] **Require measurability in `Kernel.map`.**
  `Kernel.map` now takes a measurability proof, normally synthesized by `fun_prop`; the zero fallback
  and the separate `mapOfMeasurable` constructor were removed.

- [ ] **Require s-finiteness in kernel product constructors.**
  `Kernel.compProd` in
  `Mathlib/Probability/Kernel/Composition/CompProd.lean:69` returns zero when either kernel is not
  s-finite.  Promote s-finiteness to the construction boundary for `Kernel.prod` and
  `Kernel.compProd` and migrate their consumers.

- [ ] **Make Radon--Nikodym data conditional on decomposition existence.**
  `Measure.rnDeriv` and `Measure.singularPart` in
  `Mathlib/MeasureTheory/Measure/Decomposition/Lebesgue.lean:80` and `:73` return zero without
  `HaveLebesgueDecomposition μ ν`.  Require that evidence or return a bundled decomposition; apply
  the same review to signed and complex vector-measure wrappers.

- [ ] **Move continuous functional calculus to its checked core.**
  `cfc` and `cfcₙ` in
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Unital.lean:307` and
  `Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/NonUnital.lean:215` return zero when
  the element predicate or continuity conditions fail (and,
  nonunital, when `f 0 ≠ 0`).  Make `cfcHom`/`cfcₙHom` the strict substrate and automate the
  real obligations at the primary interface.

- [ ] **Remove fake zeros at Gamma poles.**
  `Complex.Gamma` and `Real.Gamma` in
  `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean:287` and `:402` return zero at nonpositive
  integer poles.  Use pole-excluding inputs or a meromorphic-function object, with any pointwise
  extension explicitly named.

- [ ] **Separate ordinary hypergeometric functions from convergence/pole fallbacks.**
  `ordinaryHypergeometric` in
  `Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.lean:81` is zero when its defining series
  is nonsummable.  At a denominator pole `c = -k`, totalized division instead makes later
  coefficients zero and manufactures a spurious terminating polynomial with infinite convergence
  radius (lines 130 and 160); it does not make the whole function identically zero.  Require
  convergence and pole avoidance, and separately verify the analytic-continuation domain of the
  regularized hypergeometric API before using it as the total object.

- [ ] **Represent the Weierstrass function as meromorphic at lattice points.**
  `PeriodPair.weierstrassP` in
  `Mathlib/Analysis/SpecialFunctions/Elliptic/Weierstrass.lean:268` evaluates lattice poles as zero,
  and `deriv_weierstrassP` at line 593 is globally true only because derivative and function junk
  values coincide.  Expose ordinary evaluation away from the lattice and state global results at the
  meromorphic-function level.

- [ ] **Require normality for ordinal fixed-point enumerators.**
  `Ordinal.nfp` and `Ordinal.deriv` in `Mathlib/SetTheory/Ordinal/FixedPoint.lean:246` and `:325`
  accept arbitrary functions although their names promise fixed-point enumeration; several theorems
  depending on junk values are already deprecated.  Put normality/continuity evidence in the named
  interface and retain generic transfinite iteration under a distinct name.

## XL -- foundational prototypes and repository-wide migrations

- [ ] **Prototype strict inverse and division, then migrate totalized algebra in slices.**
  Follow the deferred acceptance criteria in `FORK_DESIGN.md`; this item does not authorize a
  production migration before the prototype passes them.  The inventory must include scalar
  inverse/division by zero, negative powers, rational casts, simplifier/tactic behavior, and
  `Matrix.inv` in `Mathlib/LinearAlgebra/Matrix/NonsingularInverse.lean:169`, which returns zero when
  the determinant is not a unit.  Ordinary operations require nonzero/unit evidence; useful total
  extensions remain explicitly named.  Treat Euclidean quotient/remainder as a separate design
  slice within this epic: `EuclideanDomain` requires `a / 0 = 0` and derives `a % 0 = a` in
  `Mathlib/Algebra/EuclideanDomain/Defs.lean:159` and `:152`, respectively, while a nonzero Euclidean
  divisor need not be a unit and its quotient is not exact field division.

- [ ] **Make natural subtraction and predecessor expose their domains.**
  `Nat.sub` returns zero when the subtrahend is larger, and `Nat.pred 0 = 0`; the current source calls
  these results garbage values in `Mathlib/Data/Nat/PSub.lean:15`.  Promote the existing
  `Nat.psub`/`Nat.ppred` operations, defined at lines 44 and 32, or proof-bearing wrappers requiring
  `b ≤ a`/`0 < a`, to the mathematician-facing boundary.  A separately named truncated
  subtraction/monus may remain total, but ordinary subtraction and predecessor must not silently use
  those invalid-domain zeros.  This is an XL theorem/notation migration even though the faithful
  primitives already exist; a strict public layer may bridge the Lean-core operations only after
  proving their domains.

- [ ] **Introduce strict conditional suprema and infima.**
  `ConditionallyCompleteLattice` in
  `Mathlib/Order/ConditionallyCompleteLattice/Defs.lean:46` supplies total `sSup`/`sInf` although
  their specification requires nonempty bounded sets; unbounded and empty cases receive arbitrary
  order values.  Prototype domain-bearing set/indexed operations and migrate notation carefully.
  Complete-lattice suprema/infima are not implicated.

- [ ] **Replace `Module.finrank`'s infinite-to-zero convention.**
  `Module.finrank` in `Mathlib/LinearAlgebra/Dimension/Finrank.lean:62` is
  `Cardinal.toNat (Module.rank R M)` and occurs across roughly 179 maintained Lean files.
  Natural-valued rank needs finite-rank evidence; keep cardinal rank globally.  Migrate
  `AffineSubspace.finDim` (`Mathlib/LinearAlgebra/AffineSpace/Dimension.lean:51`) and other derived
  invariants without conflating finite rank with finite generation over general semirings.

- [ ] **Make derivatives exist before they have values.**
  `fderivWithin`/`fderiv` (`Mathlib/Analysis/Calculus/FDeriv/Defs.lean:151`, `:160`),
  `derivWithin`/`deriv` (`Mathlib/Analysis/Calculus/Deriv/Basic.lean:145`, `:153`), and
  `lineDerivWithin`/`lineDeriv` (`Mathlib/Analysis/Calculus/LineDeriv/Basic.lean:100`, `:108`) return
  zero at nondifferentiable points; within-set derivatives can also be nonunique.  Build strict
  values on `Has*Deriv*`/differentiability plus unique-differentiability data, then audit every
  theorem whose statement currently relies on the zero branch.

- [ ] **Make Bochner integral notation carry existence and completeness.**
  `MeasureTheory.integral` in `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:158` returns zero
  when the function is nonintegrable or the target is incomplete.  A strict integral needs the
  function and codomain hypotheses at the public boundary; expectation and moment APIs must migrate
  with it.  The lower Lebesgue integral is not part of this defect.

- [ ] **Replace zero/one defaults for nonsummable infinite sums and products.**
  `tsum` and `tprod` in `Mathlib/Topology/Algebra/InfiniteSum/Defs.lean:132` and `:142` return zero
  and one when `HasSum`/`HasProd` fails, with additional uniqueness concerns in nonseparated spaces.
  Make `HasSum`/`HasProd` or summability/multipliability the ordinary boundary and migrate dependent
  series, products, and power-series evaluation in coherent slices.  Coordinate, rather than
  conflate, this work with the separate `finsum`-based Euler-characteristic task.

- [ ] **Split real and complex special functions from their silent extensions.**
  `Real.log` (`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean:44`) is absolute-value log off zero
  and zero at zero; `Real.sqrt` (`Mathlib/Analysis/Real/Sqrt.lean:112`) is zero on negatives;
  `Real.arcsin`/`arccos` (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean:35`, `:276`)
  clamp outside `[-1,1]`; and `Real.rpow` (`Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:35`)
  totalizes zero/negative-base cases under ordinary notation.  `Complex.log` and `Complex.arg` in
  `Mathlib/Analysis/SpecialFunctions/Complex/Log.lean:30` and
  `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean:30` assign zero at zero.  Design strict
  positive/nonnegative/interval/nonzero domains and separately name absolute, clamped, or other
  chosen extensions; preserve the legitimate principal-branch choice away from zero.  Audit
  trigonometric, entropy, logarithm, and power theorems whose unrestricted statements use fallback
  coincidences.

## Representation fidelity lint -- total objects whose representation changes the semantics

These are not undefined-operation-to-junk-value defects.  The represented object is mathematically
legitimate, but its inherited instances, indexing convention, or container shape can differ from
the standard object suggested by informal notation.  Keep this lint separate from strict-partiality
migrations: require names, types, documentation, and theorem statements to identify which object is
actually formalized, and provide a conventional facade when downstream mathematics uses another
standard representation.

- [ ] **[S] Distinguish finite product metric spaces from Euclidean space.**
  The instance for `Fin n → ℝ` is the finite Pi metric with sup distance, as documented and defined
  in `Mathlib/Topology/MetricSpace/Pseudo/Pi.lean:16` and `:30`.  Thus the distance between
  `![1, 0]` and `![0, 1]` is one.  The usual Euclidean metric is carried by
  `EuclideanSpace ℝ (Fin n)`, defined as `PiLp 2` in
  `Mathlib/Analysis/InnerProductSpace/PiL2.lean:114`, where the same distance is `√2`.  In metric or
  inner-product contexts, do not treat a bare Pi type as an unqualified Euclidean space, Euclidean
  ball, or orthonormal geometry.  It remains a faithful coordinate-vector representation of `ℝⁿ`
  when no norm or metric semantics are asserted.  Use `EuclideanSpace` for L2 geometry, or explicitly
  say that the product/sup metric is intended.  A future lint should inspect suspicious declarations
  and docstrings without rejecting genuine product-metric uses.

- [ ] **[S--M] Distinguish the zero-padded singular-value sequence from a finite singular-value
  family.**
  `LinearMap.singularValues` in
  `Mathlib/Analysis/InnerProductSpace/SingularValues.lean:94` is a countably infinite sequence whose
  finite-dimensional tail is zero.  The module documentation at lines 18--19 and 36--51 explicitly
  chooses this valid convention to avoid dependent indexing.  Keep the sequence when it is useful,
  but do not describe it without qualification as the usual finite list/family of singular values.
  Provide a finite/rank-indexed facade when a theorem or paper uses that convention, and audit
  downstream cardinality, positivity, product, and ordering statements for the intended index set.

- [ ] **[L] Distinguish zero-encoded element order from an extended order.**
  `orderOf` and `addOrderOf` in `Mathlib/GroupTheory/OrderOfElement.lean:178` encode infinite order as
  zero.  This convention is lossless because every finite order is positive and
  `orderOf_eq_zero_iff` at line 211 characterizes the sentinel; it is not an arbitrary junk value.
  Provide an extended-valued ordinary invariant and require `IsOfFinOrder`/`IsOfFinAddOrder` for a
  natural-valued projection when theorem statements perform ordinary comparisons or arithmetic that
  would misread zero.  Keep explicitly identified zero-encoding APIs where useful.

## Notation and term-structure hygiene -- valid terms with misleading surface syntax

These entries are not mathematical-unsoundness or strict-partiality findings.  They track syntax
that impersonates a general Lean application form, hides the declaration head or a meaningful
mathematical choice, cannot be found through the apparent identifier, or requires noncompositional
parser and delaborator behavior.  A notation is not defective merely because it uses brackets or
Unicode: conventional mathematical operators and literals remain appropriate when their operands
have stable roles and a searchable named declaration remains available.

- [ ] **[S] Remove the unused `Integrable[𝓐]` explicit-instance escape hatch.**
  `Mathlib/MeasureTheory/Function/L1Space/Integrable.lean:64` expands the identifier-shaped form
  directly to `@Integrable _ _ _ _ 𝓐`, but the maintained Lean trees contain no consumer beyond the
  declaration itself.  Give the anonymous σ-algebra binder a stable name if explicit application is
  needed, use ordinary named-argument syntax, and add a negative syntax test before deleting the
  notation.

- [ ] **[S--M] Remove the `P[X]` expectation macro that competes with element lookup.**
  `Mathlib/Probability/Notation.lean:48`--`:53` expands arbitrary adjacent terms `P[X]` to an
  integral and explicitly warns that the grammar conflicts with Lean's `GetElem` notation.  Prefer
  the already named integral API or the visibly symbolic `𝔼[X]` surface, then add a regression test
  that an invalid list lookup is diagnosed as a lookup error rather than reconsidered as
  expectation syntax.

- [ ] **[S] Remove the exported Diophantine proof-DSL surface.**
  `Mathlib/NumberTheory/Dioph.lean:489`--`:631` exports `D∧`, `D∨`, `D∃`, `D+`, and related notation
  for named `Dioph` closure theorems, but every maintained use is confined to that file and `D≠` and
  `D/` have no consumer.  Prefer the named lemmas where they are at least as readable; if a compact
  spelling materially helps the long internal constructions, keep it file-local rather than as a
  public parser dialect.  Remove the unused forms and verify the elaborated logical grouping of the
  subtraction, remainder, division, and Pell constructions.

- [ ] **[M] Give `ordProj` and `ordCompl` searchable declaration heads.**
  `Mathlib/Data/Nat/Factorization/Defs.lean:326`--`:334` introduces only the notations
  `ordProj[p] n` and `ordCompl[p] n`, expanding to `p ^ n.factorization p` and
  `n / ordProj[p] n`; there is no declaration with either apparent identifier.  Introduce named
  `Nat` operations, migrate the roughly 37 notation occurrences across three maintained files, and
  coordinate their mathematical domains with the separate factorization backlog.  Delete the
  identifier-shaped bracket forms after migration; any genuinely conventional symbolic surface
  should be proposed and justified separately.

- [ ] **[M] Put affine-line notation over a named affine-line declaration.**
  `Mathlib/LinearAlgebra/AffineSpace/AffineSubspace/Defs.lean:1075`--`:1077` defines
  `line[k, p₁, p₂]` only as notation for the affine span of a generated pair.  The 154 textual uses
  across 18 maintained files cannot search for or apply a declaration named by the apparent head.
  Register the conventional owner/name under the naming policy, make the notation expand through
  that declaration, and migrate canonical theorem statements to the named term.  Remove the bracket
  form unless a downstream comparison shows that it is materially clearer than ordinary
  application without reintroducing parser or discovery costs.

- [ ] **[M] Make `RatFunc K` canonical over the colliding `K⟮X⟯` notation.**
  `Mathlib/FieldTheory/RatFunc/Defs.lean:71` uses the same `⟮...⟯` delimiters as the generated-field
  macro in `Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean:529`.  With both scopes active,
  `K⟮X⟯` selects the rational-function type, so adjoining an element literally named `X` requires a
  type annotation; current workarounds include `F⟮(X : F⟮X⟯)⟯` in
  `Mathlib/NumberTheory/FunctionField.lean:207`.  Migrate the roughly 337 textual `⟮X⟯` matching
  lines across nine maintained files to the searchable `RatFunc K` head, checking each mixed nested
  use.  Retain `F⟮x₁, ..., xₙ⟯` for `IntermediateField.adjoin`: it exposes all generators, has a
  stable named expansion, and is materially clearer than spelling the generated finite set.

- [ ] **[L] Replace expected-type-driven `↧X` category bundling with visible heads.**
  `Mathlib/CategoryTheory/ConcreteCategory/Notation.lean:18`--`:35` and `:82`--`:101` infer a
  declaration named `FooCat.of` from the expected type, assume that the carrier is its final explicit
  argument, and elaborate the same visible `↧X` differently as `CommRingCat.of X`, `ModuleCat.of R X`,
  or another environment-discovered head.  The spelling has roughly 919 textual hits across 259
  maintained files.  Make the category-specific `.of` applications canonical, remove the generic
  environment search, and retain only explicit category-specific assistance if a downstream
  prototype shows that ordinary application cannot provide acceptable inference or diagnostics.

- [ ] **[L] Replace bracketed explicit-instance facades with ordinary explicit structure APIs.**
  The topology family in `Mathlib/Topology/Defs/Basic.lean:192`--`:210` and
  `Mathlib/Topology/UniformSpace/Defs.lean:206`--`:212`, `:629`--`:637` includes `IsOpen[t]`,
  `closure[t]`, `Continuous[t₁, t₂]`, `𝓤[u]`, and `UniformContinuous[u₁, u₂]`.  The measure-theory
  family includes `Measurable[𝓐, 𝓑]` at
  `Mathlib/MeasureTheory/SigmaAlgebra/Defs.lean:841`--`:845`, the strong and a.e. predicates at
  `Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:72`--`:73`,
  `Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean:75`--`:77`, and
  `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:409`--`:415`, plus the explicit `Measure` and
  `Kernel` types at `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean:77`--`:83` and
  `Mathlib/Probability/Kernel/Defs.lean:51`--`:70`.  These forms expose meaningful structures but
  encode them through a bespoke `Predicate[structure]` or `Type[structure]` application convention;
  together the spellings have roughly 568 textual hits across 87 maintained files.  Give anonymous
  instance binders stable names, choose ordinary named arguments, membership, projections, or
  explicitly parameterized named relations/types as the canonical forms, and remove their custom
  delaborators.  Preserve unsuffixed ambient predicates where one instance genuinely is ambient.

- [ ] **[L] Disambiguate the two `R[M]` monoid-algebra parsers.**
  `Mathlib/Algebra/MonoidAlgebra/Defs.lean:90`--`:123` installs the identical generic
  `term noWs "[" term "]"` grammar for `AddMonoidAlgebra R M` and `MonoidAlgebra R M`, selected only
  by scope.  Opening both scopes already produces the checked `Ambiguous term` failures in
  `MathlibTest/Algebra/MonoidAlgebra/Defs.lean:4`--`:45`.  Keep the two named type constructors as
  canonical heads; if conventional bracket notation remains, give it one deterministic elaboration
  rule or two syntactically distinct forms rather than parallel hidden heads.

- [ ] **[L] Retire the identifier-shaped manifold elaborator dialect.**
  `Mathlib/Geometry/Manifold/Notation.lean:838`--`:1013` makes bracket punctuation switch apparent
  heads such as `MDiffAt`, `MDiff`, `CMDiffAt`, `mfderiv`, `HasMFDerivAt`, `tangentMap`, and
  `UniqueMDiff` to different `*Within*` or `*On` declarations, while a custom search inspects
  expression types to recover the source and target models.  The bracketed forms alone have roughly
  1,104 textual hits across 37 maintained files.  Migrate to the existing named manifold APIs and a
  compositional mechanism for synthesizing routine model arguments; preserve their improved
  diagnostics without making an alternate identifier language the primary public syntax.

## Function-presentation hygiene -- one fact with curried and tuple views

These entries are not objections to `Function.curry`, `Function.uncurry`, `↿f`, or the
normalization lemmas that make them usable.  They track cases where beta/eta-equivalent
presentation has produced manually maintained declarations that appear to be separate
mathematical facts.  Keep a product or dependent-sum argument when it is the actual mathematical
domain, and keep structured curry/uncurry results when topology, measurability, boundedness,
linearity, or another invariant adds hypotheses or preservation content.

- [ ] **[M] Canonicalize tuple/curried duplicates for finite and infinite big operators.**
  `Mathlib/Algebra/BigOperators/Group/Finset/Sigma.lean:51`--`:101` maintains four adjacent
  `prod_*`/`prod_*'` pairs whose primed proofs are direct applications of the tuple-function
  versions; `@[to_additive]` generates the corresponding sum families.  The pattern continues in
  `Mathlib/Data/Fintype/BigOperators.lean:267`--`:293`, while
  `Mathlib/Algebra/BigOperators/Expect.lean:258`--`:270` proves `expect_product` and
  `expect_product'` separately, and
  `Mathlib/Topology/Algebra/InfiniteSum/Constructions.lean:162`--`:172` gives both
  `Multipliable.tprod_prod'` and `Multipliable.tprod_prod_uncurry` together with their additive
  versions.  Retain one theorem per product/sum/expectation fact and transport the integrand at the
  call site; correct docstrings that currently call a curried argument "uncurried."  Classify
  `prod_sigma`/`prod_sigma'` separately because the `Sigma` value may be the genuine dependent
  indexing domain rather than a presentation tuple.

- [ ] **[M] Reduce hand-written bare bridge families to a minimal generated normalization layer.**
  `Set.image_prod`, `Set.image_uncurry_prod`, and `Set.image2_curry` in
  `Mathlib/Data/Set/NAry.lean:73`--`:85` state one image computation through three spellings.
  `Mathlib/Data/Finset/NAry.lean:276`--`:281` gives both directions definitionally, and
  `Mathlib/Order/Filter/NAry.lean:53`--`:59` and `:159`--`:166` chains four manually named views of
  the same `map`/`map₂` bridge.  Audit the similarly mechanical
  `uniformContinuous₂_curry` bridge in `Mathlib/Topology/UniformSpace/Basic.lean:923`--`:936`,
  `Primrec₂.uncurry`/`Primrec₂.curry` in
  `Mathlib/Computability/Primrec/Basic.lean:325`--`:388`, and the paired pointwise-algebra
  simplification lemmas in `Mathlib/Algebra/Group/Pi/Lemmas.lean:480`--`:518` and
  `Mathlib/Algebra/Notation/Pi/Basic.lean:121`--`:129`.  Select the curried normal form where these
  are ordinary multiargument functions, retain only the `[simp]` directions needed to normalize
  boundary expressions, and generate any unavoidable compatibility names mechanically.  Do not
  remove `Primrec₂` itself merely because its implementation encodes two arguments by a product,
  and do not merge `Option.map₂_curry` with `Option.map_uncurry`: independent optional arguments
  and one optional pair are different semantic inputs.

- [ ] **[L] Prototype one product-measure and iterated-integral theorem layer, then collapse
  duplicate presentations.**
  `Mathlib/MeasureTheory/Measure/ProductBySections.lean:55`--`:60` explicitly says that many results
  are proved twice for `α → β → γ` and `α × β → γ`, with both spellings justified there by
  elaboration convenience.  Concrete pairs include `ae_ae_eq_curry_of_prod` and
  `ae_ae_eq_of_ae_eq_uncurry` at lines 342--348, the a.e.-measurable inner-integral families at
  lines 967--987, and `lintegral_productBySections`/`lintegral_lintegral` plus their symmetric
  versions at lines 1004--1078.  The same duplication occurs for measurable inner integrals in
  `Mathlib/MeasureTheory/Measure/ProductMeasure.lean:92`--`:129`, Bochner inner integrals and
  Fubini statements in `Mathlib/MeasureTheory/Integral/Prod.lean:69`--`:93` and `:461`--`:497`, and
  vector-measure inner integrals in `Mathlib/MeasureTheory/VectorMeasure/Prod.lean:229`--`:256`.
  Prototype the canonical statement for each family against current elaboration-sensitive
  consumers, taking account of whether the product is the actual domain and which equality
  orientation is the useful rewrite normal form.  Make the other spelling a documentation/search
  view or an inline transport through `Function.curry`/`Function.uncurry`, not another hand-written
  proof.  If compatibility still requires a named entry, generate the exact transport mechanically
  under the compatibility policy.  Preserve genuine Tonelli, Fubini, measurability, integrability,
  and change-of-order results; migrate consumers together and negative-scan only the hand-maintained
  duplicate proofs and any names the prototype actually retires.

- [ ] **[L] Add an elaborated-statement lint for redundant presentation declarations.**
  A 2026-09-12 source scan found 621 curry/uncurry-named declaration lines in 114 files among all
  9,108 tracked Lean files.  Here a named line begins with an optional `protected`, `private`, or
  `noncomputable` modifier followed by `def`, `abbrev`, `theorem`, or `lemma`, and its declared
  identifier contains case-insensitive `curry`, `curried`, `currying`, or `uncurr*`; this lexical
  query was rerun at the final documentation state.  Suffixes and textual call counts alone were too
  noisy to classify the matches.
  Prototype a lint that normalizes only the bare `Function.curry`/`Function.uncurry`,
  `Sigma.curry`/`Sigma.uncurry`, and recursive `↿f` transports, compares theorem propositions
  modulo beta/eta conversion, and reports a candidate only when an existing declaration supplies
  the same mathematical fact.  Use the measure/integral and big-operator pairs above as positive
  controls.  Negative controls include `ContinuousMap.uncurry` and `Homeomorph.curry` in
  `Mathlib/Topology/CompactOpen.lean:430`--`:471` and `:556`, the multilinear and continuous
  multilinear equivalences in `Mathlib/LinearAlgebra/Multilinear/Curry.lean` and
  `Mathlib/Analysis/Normed/Module/Multilinear/Curry.lean`, categorical closed-structure currying,
  and genuine product, tensor, direct-sum, finite-support, or dependent-sum domains.  Companion
  normalization lemmas for an admitted structured construction inherit that construction's
  exclusion.  Run the lint in audit mode over the inherited tree and as a diff-scoped warning for
  new declarations before considering repository-wide enforcement.

## Proof and API-boundary hygiene -- rewrites that depend on extra transparency

`erw` is logically sound, but its success where `rw` fails can expose a missing public rewrite
lemma, a coercion or representation boundary, or definitional-equality dependence in downstream
proofs.  Treat each occurrence as API-debt evidence to classify, not as proof that every occurrence
has the same root cause.  Repair the exposed interface or proof normal form before mechanically
changing the tactic.

- [ ] **[L] Eliminate `erw` invocations from maintained proofs.**
  The current maintained Lean trees contain 430 tactic invocations across 191 files (426 across 189
  `Mathlib/` files).  Several sites already identify an API or definitional-equality problem:
  `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean:167`--`:171` attributes its `erw` to a
  `map_top` composition mismatch; `Mathlib/RingTheory/QuasiFinite/Weakly.lean:204` says its use
  should disappear when `Ideal.map` stops taking hom classes; and
  `Mathlib/RingTheory/Ideal/IsPrincipal.lean:110`--`:113` explains that the rewrite sees through an
  equality between two subtype presentations.  Inventory the occurrences by missing lemma,
  coercion/representation mismatch, category-composition defeq abuse, and genuine elaborator
  limitation.  For each family, add the natural public lemma or stable normal form and migrate its
  consumers to `rw`, `simp`, `change`, or an explicit equality transport that records the intended
  boundary.  Use `Mathlib/Tactic/CategoryTheory/CheckCompositions.lean:20` where applicable to
  diagnose composition discrepancies.  Finish with a repository-wide negative scan for tactic
  invocations; documentation and the `erw?` diagnostic implementation are outside this migration
  unless their own APIs become obsolete.

## Resolved classification audits

The 2026-09-13 classification pass resolved the families below against the strict-domain and
compositional-notation contracts.  A checked item records a classification decision, not completion
of any open migration task that it references:

- [x] **`finsum`/`finprod` are explicit finite-support extensions.**  Their names, definition
  docstrings, notation docstrings, and theorem families identify the zero/one result on infinite
  support, so the core operations are excluded from the silent-totalization backlog.  The existing
  `eulerChar` task remains open because an ordinary integer-valued invariant must not inherit either
  that fallback or `finrank`'s infinite-to-zero convention.
- [x] **Matroid closure needs a strict ordinary boundary.**  Intersecting with `M.E` is an intentional
  implementation convention, but the ordinary `closure` name does not identify that extension and
  the module already provides the domain-bearing `subtypeClosure`.  The L task above records the
  canonical migration.
- [x] **Local bundle representatives split at the exported coordinate API.**  Globally defined
  trivialization representatives may retain irrelevant values outside their base sets when every
  semantic statement proves independence from them.  Ordinary `coordChange` operations expose those
  values under a mathematical name, so the M task above moves their overlap into the public domain.
- [x] **`Polynomial.natDegree` is an explicit natural-valued projection.**  The faithful
  `Polynomial.degree : WithBot ℕ` remains public, the zero convention is documented, and bridges to
  `natDegree` require nonzeroness where it matters.  Do not promote the projection wholesale; audit a
  paper-facing consumer only when it omits evidence needed by its intended statement.
- [x] **Computational decoders and searches are excluded by default.**  Explicit `getD`, `headI`, tape
  blanks, parser defaults, and noncanonical decoders belong to computational representation
  contracts.  Reopen a case only when it is exported as a checked mathematical inverse or primary
  mathematical workflow.
- [x] **Witness choice alone is not a defect.**  `LinearIndependent.repr` in
  `Mathlib/LinearAlgebra/LinearIndependent/Defs.lean:462` is the positive control: its input carries
  both linear independence and span membership and the implementation is the inverse of a proved
  linear equivalence.  Continue to flag reachable invalid branches or names asserting unsupported
  uniqueness; the existing `Function.invFun`, `Function.extend`, and `LinearMap.leftInverse` tasks
  are such separate cases.
- [x] **An explicit default is neither automatically faithful nor automatically defective.**  Keep
  technical representative constructors behind proved boundaries.  Promote a concrete operation
  when users are asked to write the defaulted surrogate in place of the mathematical object;
  integration-facing `ContinuousMap.mkD` remains the positive migration case above.
- [x] **Conditional expectation and probability brackets are conventional secondary surfaces.**
  `μ[f | 𝓐]`, `μ[|s]`, and `μ[t | s]` have stable named expansions, preserve nesting, and elaborate
  correctly when both scopes are active.  Keep the notation; the domain defects in `condExp` and
  `ProbabilityTheory.cond` remain separate strictness tasks.
- [x] **The audited Unicode and indexed shortcuts remain admissible.**  `πₓ`/`πₘ`, `⦋m⦌ₙ`,
  generated intermediate fields, and `Mᵐ⁰` expose stable operands and expand through documented
  named structures or functor operations; the truncated-simplex proof is routine and can also be
  supplied explicitly.  Search inconvenience alone does not justify migration.
- [x] **The shared field delimiters and Diophantine DSL split into distinct outcomes.**  Keep
  `F⟮x₁, ..., xₙ⟯` as the conventional secondary surface for `IntermediateField.adjoin`, migrate the
  colliding rational-function `K⟮X⟯` surface to `RatFunc K`, and remove or localize the exported
  `Dioph` proof dialect as recorded in the notation tasks above.

## Audit coverage and limits

The 2026-09-11 pass searched the current working-tree source across 9,063 Lean files (about 1.93
million lines) in `Mathlib/`, `MathlibTest/`, `Archive/`, `Counterexamples/`, and `Wanted/`.  Candidate
generation included explicit junk/arbitrary-value language, choice without witnesses, lossy
`.toNat`/`.toReal`/`.unzeroD` conversions, zero/one branches, conditional suprema/infima, `erw`
invocations, and failure lemmas for summability, integrability, differentiability, measurability,
and finiteness.
The public definitions above were then inspected by mathematical domain rather than accepted from
keyword matches alone.

The scan deliberately excludes `.lake/`, `Cache/`, generated dependencies, and ordinary test-only or
metaprogramming defaults from the public mathematical backlog.  It is a high-confidence inventory,
not a declaration-by-declaration proof of completeness: a mathematically misleading abstraction can
have no textual marker, and final migration order still needs dependency prototypes and real
downstream formalizations.  New findings should be inserted by coherent migration effort, not by
discovery date.

A separate 2026-09-11 notation pass inspected 5,641 term-syntax declaration lines in the same 9,063
Lean files and manually classified 52 identifier-attached bracket declarations, together with
explicit-instance expansions, custom elaborators, delaborators, and representative consumers.  It
promotes only families with a hidden ordinary/instance argument, a missing or ambiguous declaration
head, or a concrete parser collision.  Conventional polynomial, algebraic-adjoin, tensor, valuation,
expectation, variance, and literal notations were screened rather than added automatically when
their operands and named APIs remained compositional and discoverable.

A 2026-09-12 function-presentation pass scanned all 9,108 tracked Lean files, including the 9,076
files in `Mathlib/`, `MathlibTest/`, `Archive/`, `Counterexamples/`, and `Wanted/`.  The pass
inspected 621 curry/uncurry-named declaration lines in 114 files, together with tuple-function
versus curried-function binders, primed theorem pairs, and source comments that explicitly describe
duplicated presentations.  The only named hit outside `Mathlib/` was the unfolding fixture at
`MathlibTest/FunPropMinimal.lean`; no non-`Mathlib/` public theorem family was promoted.  The scan
manually separated beta/eta transport from structured topology, measurability, multilinearity,
category theory, finite-support, and genuine product or dependent-sum mathematics.  It cannot prove
the absence of arbitrarily named equivalent theorems with no presentation marker; the proposed
elaborated-statement lint is the
required next probe for that boundary.
