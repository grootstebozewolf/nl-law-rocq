(** * Combined levy minus heffingskortingen, art. 8.8 (non-refundability).

    Model person: resident, below AOW age the whole year, born after 1945,
    whose only income is wages, with no deductions.  Then
      belastbaar inkomen box 1 = premie-inkomen (art. 8 lid 1 Wfsv)
        = verzamelinkomen (art. 2.18) = arbeidsinkomen (art. 8.1 lid 1 e) = y.
    Only the algemene heffingskorting and arbeidskorting are claimed. *)
From Stdlib Require Import ZArith Lia.
From NLLaw Require Import Params2026 Box1 Kortingen.
Open Scope Z_scope.

(** Standaardheffingskorting (art. 8.2), restricted to a + b. *)
Definition kort (y : Z) : Z := ahk y + ak y.

(** Art. 8.8: "De gecombineerde heffingskorting bedraagt maximaal het bedrag
    van de gecombineerde inkomensheffing."  (The split into an IB part,
    8,10/35,75, and premium parts, art. 8.3-8.6, and the cross-offset of
    art. 9 lid 2 Wfsv, do not change the combined total, so we model the
    combined amounts directly.) *)
Definition applied (y : Z) : Z := Z.min (kort y) (levy y).

(** Net amount payable on box 1 (IB + premie volksverzekeringen). *)
Definition net (y : Z) : Z := levy y - applied y.

Theorem kort_nonneg : forall y, 0 <= kort y.
Proof. intros; pose proof (ahk_bounds y); pose proof (ak_bounds y); unfold kort; lia. Qed.

Theorem kort_max : forall y, kort y <= sc (euro 3115 + euro 5685).
Proof. intros; pose proof (ahk_bounds y); pose proof (ak_bounds y); unfold kort;
       unfold ahk_max, ak_abc_max, sc, S, euro in *; lia. Qed.

(** Art. 8.8 as a theorem: the credits actually granted never exceed the
    levy, so the net amount is never negative (no negative income tax). *)
Theorem applied_le_levy : forall y, applied y <= levy y.
Proof. intros; unfold applied; lia. Qed.

Theorem applied_le_kort : forall y, applied y <= kort y.
Proof. intros; unfold applied; lia. Qed.

Theorem applied_nonneg : forall y, 0 <= applied y.
Proof. intros; pose proof (kort_nonneg y); pose proof (levy_nonneg y);
       unfold applied; lia. Qed.

Theorem net_nonneg : forall y, 0 <= net y.
Proof. intros; pose proof (applied_le_levy y); unfold net; lia. Qed.

Theorem net_le_levy : forall y, net y <= levy y.
Proof. intros; pose proof (applied_nonneg y); unfold net; lia. Qed.

(** ** Closed forms of the levy per row of art. 2.10. *)
Lemma levy_r1 : forall y, 0 <= y <= b1 -> levy y = r_comb * y.
Proof. intros; unfold r_comb; unfold_box1; cbv zeta; split_ifs; lia. Qed.

Lemma levy_r2 : forall y, b1 < y <= b2 ->
  levy y = sc colIII_2 + r_ib2 * (y - b1) + r_prem * b1.
Proof. intros; unfold_box1; cbv zeta; split_ifs; lia. Qed.

Lemma levy_r3 : forall y, b2 < y ->
  levy y = sc colIII_3 + r_ib3 * (y - b2) + r_prem * b1.
Proof. intros; unfold_box1; cbv zeta; split_ifs; lia. Qed.

Lemma net_slack : forall y, kort y <= levy y -> net y = levy y - kort y.
Proof. intros; unfold net, applied; lia. Qed.

Lemma net_capped : forall y, levy y <= kort y -> net y = 0.
Proof. intros; unfold net, applied; lia. Qed.

(** ** The cap of art. 8.8 really binds: below € 11.357,84 the credits
    exceed the levy and part of them is lost (they are not paid out). *)
Theorem cap_binds_low : forall y, 0 <= y <= euro 11357 + 83 -> net y = 0.
Proof.
  intros y Hy. apply net_capped. unfold kort.
  rewrite (levy_r1 y) by (unfold b1, euro in *; lia).
  rewrite (ahk_full y) by (unfold ahk_thr, euro in *; lia).
  rewrite (ak_band_a y) by (unfold ak_b_thr, euro in *; lia).
  unfold r_comb, r_ib1, r_prem, r_aow, r_anw, r_wlz, ahk_max, ak_a, sc, S, euro in *; lia.
Qed.

Theorem credits_lost_example : applied (euro 10000) < kort (euro 10000).
Proof. vm_compute. reflexivity. Qed.

Theorem net_pos_above : forall y, euro 11357 + 84 <= y -> 0 < net y.
Proof.
  intros. unfold net, applied, kort, levy.
  unfold_box1; unfold_kort; cbv zeta; split_ifs; lia.
Qed.
