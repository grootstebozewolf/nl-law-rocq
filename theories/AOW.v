(** * Variant: taxpayer at AOW age the whole of 2026, born on/after 1-1-1946.

    - Box-1 tax: same art. 2.10 table (art. 2.10a applies only to those
      born before 1946).
    - Premie: no AOW premium (art. 10 lid 2 Wfsv), so only Anw 0,10% +
      Wlz 9,65% on premie-inkomen capped at b1.
    - Heffingskortingen: the standaardheffingskorting is split into an IB
      part (8,10/35,75, art. 8.3) and premium parts (art. 8.4-8.6); by
      art. 12 lid 1 Wfsv the AOW part (17,90/35,75) is only granted to those
      paying AOW premium.  Hence an AOW-age person keeps 17,85/35,75 of it.
      We floor at 1/100000 cent (negligible).
    - Ouderenkorting (art. 8.17) and alleenstaande-ouderenkorting are NOT
      modelled. *)
From Stdlib Require Import ZArith Lia.
From NLLaw Require Import Params2026 Box1 Kortingen Combined.
Open Scope Z_scope.

Definition r_keep_aow : Z := r_ib1 + r_anw + r_wlz.  (* 17,85 *)

Definition premie_aow (y : Z) : Z := (r_anw + r_wlz) * Z.min (clamp0 y) b1.
Definition levy_aow (y : Z) : Z := ib_box1 y + premie_aow y.
Definition kort_aow (y : Z) : Z := (kort y * r_keep_aow) / r_comb.
Definition applied_aow (y : Z) : Z := Z.min (kort_aow y) (levy_aow y).
Definition net_aow (y : Z) : Z := levy_aow y - applied_aow y.

Theorem net_aow_nonneg : forall y, 0 <= net_aow y.
Proof. intros; unfold net_aow, applied_aow; lia. Qed.

Theorem kort_aow_le_kort : forall y, 0 <= kort_aow y <= kort y.
Proof.
  intros y. pose proof (kort_nonneg y). unfold kort_aow, r_keep_aow, r_comb,
    r_ib1, r_prem, r_aow, r_anw, r_wlz.
  split.
  - apply Z.div_pos; lia.
  - apply Z.div_le_upper_bound; lia.
Qed.

(** First-bracket combined rate for an AOW-age person: 8,10 + 9,75 = 17,85 %,
    matching the Belastingdienst table. *)
Lemma levy_aow_r1 : forall y, 0 <= y <= b1 -> levy_aow y = 17850 * y.
Proof.
  intros; unfold levy_aow, premie_aow, r_anw, r_wlz; unfold_box1; cbv zeta;
  split_ifs; lia.
Qed.

(** ** Finding: the statutory AHK for an AOW-age person at low income is
    3.115 x 17,85/35,75 = € 1.555,32, whereas the Belastingdienst table
    ("Tabel algemene heffingskorting 2026", AOW-leeftijd hele jaar) shows
    € 1.556; the phase-out rate 6,398 x 17,85/35,75 = 3,1945 % does match
    the published 3,195 %.  The Belastingdienst's own footnote says the
    table can deviate "een enkele euro" through rounding.  Source:
    https://www.belastingdienst.nl/wps/wcm/connect/bldcontentnl/belastingdienst/prive/inkomstenbelasting/heffingskortingen_boxen_tarieven/heffingskortingen/algemene_heffingskorting/tabel-algemene-heffingskorting-2026 *)
Example ahk_aow_low : (ahk 0 * r_keep_aow) / r_comb = 15553216783.
Proof. vm_compute. reflexivity. Qed.

Theorem ahk_aow_below_published : (ahk 0 * r_keep_aow) / r_comb < sc (euro 1556).
Proof. vm_compute. reflexivity. Qed.

(** ** Art. 2.10a (born before 1946): column III is again the floor. *)
Theorem colIII_pre46_floor :
  sc colIII_2_pre46 <= r_ib1 * b1_pre46 < sc colIII_2_pre46 + sc (euro 1) /\
  sc colIII_3_pre46 <= sc colIII_2_pre46 + r_ib2 * (b2 - b1_pre46)
                     < sc colIII_3_pre46 + sc (euro 1).
Proof. vm_compute. repeat split; discriminate. Qed.

(** Top-band marginal rate for an AOW-age employee at € 100.000:
    49,50 + 6,51 x 17,85/35,75 = 52,7504 % (vs 56,01 % below AOW age). *)
Example aow_step_100k : net_aow (euro 100001) - net_aow (euro 100000) = 5275044. (* 52,75044 cent; exact slope 52,750420, difference is the 1/100000-cent flooring *)
Proof. vm_compute. reflexivity. Qed.
