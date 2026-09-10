# Mathematical fidelity backlog

This file records public mathematical interfaces that should be audited or migrated under the
strict-domain policy in `FORK_DESIGN.md`.  It is an implementation backlog, not a claim that Lean is
unsound and not a claim that every total implementation is defective.  A documented fallback is
still non-strict when the ordinary public operation erases its mathematical domain.  An explicitly
named/default-taking extension is not a *silent-totalization* defect, but that fact alone does not
make it mathematician-facing: it can still be the wrong primary interface if papers would instead
state a domain condition, work on a constrained object, or pass to an a.e.-equivalence class.  An
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

For every migration below:

1. expose definedness through an input type, proof argument, or explicit partiality;
2. give any retained total extension a name that identifies its fallback;
3. audit theorem statements that currently succeed on the invalid-domain branch;
4. preserve a proved bridge on the valid domain and record interface strictness separately from
   implementation strictness;
5. add negative tests showing that strict code cannot recover the old fallback, including after
   simplification; and
6. run targeted builds plus the affected downstream tests at the final source state.

## S -- bounded corrections and strict facades

- [ ] **Correct the stale `Measure.map` module overview.**
  `Mathlib/MeasureTheory/Measure/Map.lean:17` says that a non-a.e.-measurable map yields zero, but
  `Measure.map` at lines 99--106 yields an arbitrary Dirac mass when the source measure is nonzero.
  This documentation correction is independent of the L API migration below.

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

## M -- subsystem migrations

- [ ] **Make finite multiplicity a checked projection.**
  `Mathlib/RingTheory/Multiplicity.lean:47` defines `multiplicity` as
  `(emultiplicity a b).toNat`, so infinite multiplicity becomes zero.  Keep `emultiplicity` as the
  faithful invariant and require `FiniteMultiplicity` for a natural-valued projection.

- [ ] **Require monicity for polynomial division-by-monic notation.**
  `Polynomial.divByMonic` and `Polynomial.modByMonic` in
  `Mathlib/Algebra/Polynomial/Div.lean:132` and `:137` accept a nonmonic divisor and return quotient
  zero and the original dividend.  Thread `q.Monic` through `/ₘ` and `%ₘ`, reusing
  `divModByMonicAux`.

- [ ] **Exclude the zero polynomial from `Polynomial.rootMultiplicity`.**
  `Mathlib/Algebra/Polynomial/Div.lean:498` returns zero for the zero polynomial even though a
  largest dividing power does not exist.  Require `p ≠ 0` or retain infinity in the result.

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

- [ ] **Put natural factorization on nonzero inputs.**
  `Nat.factorization` in `Mathlib/Data/Nat/Factorization/Defs.lean:50` gives zero multiplicities at
  zero, and `Nat.primeFactors` in `Mathlib/Data/Nat/PrimeFin.lean:37` gives the empty set although
  every prime divides zero.  Use a positive/nonzero carrier or explicit failure and migrate the
  arithmetic infrastructure as a unit.

- [ ] **Migrate natural cardinalities away from infinity-to-zero.**
  `Nat.card` in `Mathlib/SetTheory/Cardinal/Finite.lean:41` and `Set.ncard` in
  `Mathlib/Data/Set/Card.lean:613` return zero on infinite inputs.  Require `Finite α`/`s.Finite` for
  natural values and use `ENat.card`/`Set.encard` globally.

- [ ] **Make lossy extended-value conversions checked or explicitly defaulted.**
  `ENat.toNat` (`Mathlib/Data/ENat/Basic.lean:118`), `Cardinal.toNat`
  (`Mathlib/SetTheory/Cardinal/ToNat.lean:31`), and `ENNReal.toNNReal`/`toReal`
  (`Mathlib/Basic/ENNReal/Basic.lean:225`) send infinity to zero.  Provide proof-bearing finite
  conversions and reserve `...OrZero`-style names for the current maps.

- [ ] **Separate chosen preimages from true inverse functions.**
  `Function.invFun` in `Mathlib/Logic/Function/Basic.lean:526` picks an arbitrary element outside
  the range and a chosen preimage for noninjective maps.  Use equivalences/bijections for inverse
  functions and a range-indexed chosen-preimage operation for the weaker construction.

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

- [ ] **Make measure pushforward require a.e. measurability.**
  `Measure.map` in `Mathlib/MeasureTheory/Measure/Map.lean:99` returns an arbitrary Dirac mass for a
  non-a.e.-measurable function and nonzero source measure.  Its valid branch already uses an
  a.e.-measurable representative at lines 101--102, and core results such as `map_apply` and
  `map_map` already carry measurability evidence.  Promote that evidence to the construction
  boundary, explicitly name any retained fallback, and migrate the roughly 100 qualified-use files
  plus `FiniteMeasure.map`, `ProbabilityMeasure.map`, conditional-law, and kernel wrappers.  A new
  strict facade is M-sized; making it canonical throughout the existing ecosystem is L-sized.

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

- [ ] **Require measurable random variables for conditional distributions.**
  `ProbabilityTheory.condDistrib` in `Mathlib/Probability/Kernel/CondDistrib.lean:64` constructs a
  joint pushforward for arbitrary `X` and `Y`, inheriting `Measure.map`'s arbitrary-Dirac fallback.
  Require joint a.e. measurability; retain normal freedom to choose versions on null conditioning
  fibres.

- [ ] **Require measurability and s-finiteness in kernel map/product constructors.**
  `Kernel.map` in `Mathlib/Probability/Kernel/Composition/MapComap.lean:63` returns zero for a
  nonmeasurable map, while `Kernel.compProd` in
  `Mathlib/Probability/Kernel/Composition/CompProd.lean:69` returns zero when either kernel is not
  s-finite.  Promote `mapOfMeasurable`-style constructors and evidence-bearing composition products.

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
  extensions remain explicitly named.

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

## Classification audits before adding more migration tasks

The following families contain total implementation values but are not yet established as public
fidelity defects.  Resolve the stated distinction before promoting them into the effort-ranked
backlog:

- [ ] **`finsum`/`finprod`:** decide whether their names and finite-support contract already identify
  the zero/one extension on infinite support.  Regardless of that decision, ordinary invariants such
  as `eulerChar` must not expose the fallback silently.
- [ ] **Matroid closure outside the ground set:**
  `Mathlib/Combinatorics/Matroid/Closure.lean:134` intersects an arbitrary set with `M.E`.  Determine
  whether this is the intended ambient-ground-set convention or whether ordinary closure should take
  a ground-set subtype.
- [ ] **Local bundle representatives:** distinguish globally defined representatives whose values are
  explicitly irrelevant outside a base set from exported coordinate operations that allow those
  values to affect statements.
- [ ] **Zero-extended singular-value sequences:** determine whether zeros after the finite-dimensional
  range are the canonical sequence convention or whether the public indexing domain should be
  finite-rank data.
- [ ] **Natural-valued projections of extended invariants:** review operations such as
  `Polynomial.natDegree` in `Mathlib/Algebra/Polynomial/Degree/Defs.lean:52`, which maps the zero
  polynomial's faithful `WithBot` degree to zero.  A codomain-indicating name makes the projection
  visible but does not by itself establish that a paper-facing API should omit the nonzero proof.
- [ ] **Computational decoders and searches:** leave explicit `getD`, `headI`, tape blanks, parser
  defaults, and noncanonical decoding out of the *silent-totalization* list, but still review any one
  promoted as a mathematician-facing checked inverse or primary mathematical workflow.
- [ ] **Chosen witnesses:** do not flag `Classical.choose` merely for noncanonicity when a public proof
  establishes that a valid witness exists; flag it only when the invalid-domain branch is reachable
  or the name asserts uniqueness/canonicity not supplied by the hypotheses.
  `LinearIndependent.repr` in `Mathlib/LinearAlgebra/LinearIndependent/Defs.lean:462` is the positive
  control: its input carries linear independence and lies in the span, and the implementation is the
  inverse of a proved linear equivalence.
- [ ] **Explicit default constructors:** do not infer fidelity merely from a `D` suffix or a visible
  fallback argument.  Check whether the operation is only technical glue behind an invariant result,
  or whether users are being asked to write a defaulted surrogate where ordinary mathematics uses a
  domain-bearing object.  `ContinuousMap.mkD` is promoted above because its integration-facing use
  falls in the latter category.

## Audit coverage and limits

The 2026-09-11 pass searched the current working-tree source across 9,063 Lean files (about 1.93
million lines) in `Mathlib/`, `MathlibTest/`, `Archive/`, `Counterexamples/`, and `Wanted/`.  Candidate
generation included explicit junk/arbitrary-value language, choice without witnesses, lossy
`.toNat`/`.toReal`/`.unzeroD` conversions, zero/one branches, conditional suprema/infima, and
failure lemmas for summability, integrability, differentiability, measurability, and finiteness.
The public definitions above were then inspected by mathematical domain rather than accepted from
keyword matches alone.

The scan deliberately excludes `.lake/`, `Cache/`, generated dependencies, and ordinary test-only or
metaprogramming defaults from the public mathematical backlog.  It is a high-confidence inventory,
not a declaration-by-declaration proof of completeness: a mathematically misleading abstraction can
have no textual marker, and final migration order still needs dependency prototypes and real
downstream formalizations.  New findings should be inserted by coherent migration effort, not by
discovery date.
