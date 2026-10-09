import CountingMatroid.Analysis.ObservationRoundDrawSites
import CountingMatroid.Analysis.ObservationRoundDrawSiteCovered
import CountingMatroid.Analysis.StoppingDrawPrefixCover
import CountingMatroid.Analysis.FiniteSuffixDrawAbortMass
import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.ObservePhaseIntervalReplay
import CountingMatroid.Analysis.RestartPhaseIntervalReplay

set_option autoImplicit false

/-!
The operational boundary needed by the observation-abort union bound.
A reached failing round is represented by two prefixes of the actual
observation loop. The cover assembly is proved from the concrete stopping
site locality/abort-attribution and finite-block coverage obligations in the
support files. Those two support theorems remain open, so this file does
not yet establish the observation-abort bound without proof debt.
No stochastic conclusion is assumed here.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawCover

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.FiniteSuffixDrawAbortMass

/-- INTERNAL: Construct the three actual draw-site prefix families for one
reached failing observation round. This is an operational statement: its
families are prefix-free, their denominators positive, and every trial lies
inside the remaining suffix. A draw abort on the original tape covers each
round failure; classifier/selection failures must first be ruled out.
TEXLINE: main.tex:1177-1187,1382-1421 -/
theorem observation_round_draw_cover (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (k : ℕ) (hk : k < (CountingMatroid.Interface.Pseudocode.setup n p).observations) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    ∃ covers : Fin 3 → DrawPrefixCover s.drawTrials t,
      ∀ suffix : List Bool, suffix.length = t →
        ReachedObservationRoundAbort n r o₁ o₂ p j pref k suffix →
        ∃ site : Fin 3, ∃ head ∈ (covers site).prefixes,
          head <+: suffix ∧
          (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
            s.drawTrials ((covers site).denominator head)
            (pref.length + head.length)).val.1 = none := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
  obtain ⟨hlocal, habort⟩ :=
    ObservationRoundDrawSites.observation_round_draw_sites n r M₁ M₂ o₁ o₂ p
      hn hfull hr h₁ h₂ hpositive j hj pref hprefix k hk
  have hcoverage :=
    ObservationRoundDrawSiteCovered.observation_round_draw_site_covered n r M₁ M₂ o₁ o₂ p
      hn hfull hr h₁ h₂ hpositive j hj pref hprefix k hk
  let stop : Fin 3 → List Bool → Option (ℕ × ℕ) := fun site suffix =>
    (ObservationRoundDrawSites.observationDrawSite n r o₁ o₂ p j pref k site suffix).map
      (fun d => (d.1 - pref.length, d.2))
  have hbound (site : Fin 3) (suffix : List Bool) (hlen : suffix.length = t)
      (d : ℕ × ℕ) (hd : stop site suffix = some d) :
      0 < d.2 ∧ d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤ t := by
    obtain ⟨absolute, hsite, heq⟩ := Option.map_eq_some_iff.mp hd
    have hc := hcoverage site suffix hlen absolute hsite
    have hp := ObservationRoundDrawSites.observationDrawSite_positive n r o₁ o₂ p j
      pref k site suffix absolute hn hsite
    change (absolute.1 - pref.length, absolute.2) = d at heq
    subst d
    refine ⟨hp, ?_⟩
    dsimp only [s, t]
    omega
  have hstoplocal (site : Fin 3) (suffix : List Bool) (hlen : suffix.length = t)
      (d : ℕ × ℕ) (hd : stop site suffix = some d)
      (other : List Bool) (hother : other.length = t)
      (htake : suffix.take d.1 <+: other) : stop site other = some d := by
    obtain ⟨absolute, hsite, heq⟩ := Option.map_eq_some_iff.mp hd
    change (absolute.1 - pref.length, absolute.2) = d at heq
    subst d
    have heq' := hlocal site suffix hlen absolute hsite other hother htake
    simp only [stop, heq', Option.map_some]
  have hcoverExists (site : Fin 3) :=
    StoppingDrawPrefixCover.stopping_draw_prefix_cover s.drawTrials t (stop site)
      (hbound site) (hstoplocal site)
  choose covers hcovers using hcoverExists
  refine ⟨covers, ?_⟩
  intro suffix hlen hbad
  obtain ⟨site, d, hsite, hfailed⟩ := habort suffix hlen hbad
  have hstop : stop site suffix = some (d.1 - pref.length, d.2) := by
    simp only [stop, hsite, Option.map_some]
  obtain ⟨head, hhead, hprefixHead, hlength, hdenominator⟩ :=
    hcovers site suffix hlen (d.1 - pref.length, d.2) hstop
  have hc := hcoverage site suffix hlen d hsite
  refine ⟨site, head, hhead, hprefixHead, ?_⟩
  rw [hdenominator, hlength, Nat.add_sub_of_le hc.1]
  exact hfailed

end CountingMatroid.Analysis.ObservationRoundDrawCover

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r27 · still open · the cover assembly checks, but stopped-site locality/abort attribution and the tight finite-block bound remain unproved after two opaque mechanical admission rejections; every support file is retained.

* r27 · rejected handoff · the public-name packet received mechanical admission rejected without a diagnostic; all support files retained and all source checks and targeted builds passed.

* r27 · rejected handoff · the first packet was rejected by declaration-name validation; resubmitting with public declaration names while retaining every support file.

* r27 · assembled · proved cover construction from concrete stopped-site locality, abort attribution, and quantitative cursor/width coverage; relocated ReachedObservationRoundAbort unchanged into ObservationRoundDrawSites to avoid an import cycle.

* r26 · attempted · unfolding a successful restart and exhaustive aesop leaves non-invalid classification of the nested trace-return fold endpoint; replay alone cannot discharge this invariant.

* r26 · decomposed · stated the operational draw-cover construction separately from the fair-suffix sampling law, retaining successful histories and exact capped-draw locations.
-/
