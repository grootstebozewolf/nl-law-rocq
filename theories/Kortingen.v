(** * Heffingskortingen: algemene heffingskorting (art. 8.10) and
      arbeidskorting (art. 8.11) Wet IB 2001, 2026.  Scaled units. *)
From Stdlib Require Import ZArith Lia.
From NLLaw Require Import Params2026 Box1.
Open Scope Z_scope.

(** ** Art. 8.10 lid 2.  [v] = verzamelinkomen (cents). *)
Definition ahk (v : Z) : Z :=
  Z.max 0 (sc ahk_max - ahk_rate * Z.max 0 (v - ahk_thr)).

(** ** Art. 8.11 lid 2, eerste volzin, transcribed clause by clause.
    [w] = arbeidsinkomen (cents).
    (The second sentence, a floor equal to the wage-tax arbeidskorting
    of art. 22a Wet LB 1964 for w <= € 45.592, is NOT modelled.) *)
Definition ak_part_a  (w : Z) : Z := Z.min (ak_a * clamp0 w) (sc ak_a_max).
Definition ak_part_ab (w : Z) : Z :=
  Z.min (ak_part_a w + ak_b * Z.max 0 (w - ak_b_thr)) (sc ak_ab_max).
Definition ak_part_abc (w : Z) : Z :=
  Z.min (ak_part_ab w + ak_c * Z.max 0 (w - ak_c_thr)) (sc ak_abc_max).
Definition ak (w : Z) : Z :=
  Z.max 0 (ak_part_abc w - ak_d * Z.max 0 (w - ak_d_thr)).

Ltac unfold_kort :=
  unfold ahk, ak, ak_part_abc, ak_part_ab, ak_part_a, clamp0,
    ahk_max, ahk_thr, ahk_rate, ak_a, ak_a_max, ak_b, ak_b_thr, ak_ab_max,
    ak_c, ak_c_thr, ak_abc_max, ak_d, ak_d_thr, sc, S, euro in *.

(** ** Bounds *)
Theorem ahk_bounds : forall v, 0 <= ahk v <= sc ahk_max.
Proof. intros; unfold_kort; lia. Qed.

Theorem ak_bounds : forall w, 0 <= ak w <= sc ak_abc_max.
Proof. intros; unfold_kort; lia. Qed.

(** AHK is non-increasing in the verzamelinkomen. *)
Theorem ahk_antitone : forall v1 v2, v1 <= v2 -> ahk v2 <= ahk v1.
Proof. intros; unfold_kort; lia. Qed.

(** AHK is the full € 3.115 up to € 29.736 and nil from € 78.424 on
    (the statutory zero point is 29.736 + 3.115/6,398% = € 78.423,09...,
     a little BELOW the € 78.426 that the Belastingdienst table uses as the
     end of the phase-out band). *)
Theorem ahk_full : forall v, v <= ahk_thr -> ahk v = sc ahk_max.
Proof. intros; unfold_kort; lia. Qed.

Theorem ahk_zero : forall v, euro 78423 + 9 <= v -> ahk v = 0.
Proof. intros; unfold_kort; lia. Qed.

Theorem ahk_pos_until : forall v, v <= euro 78423 + 8 -> 0 < ahk v.
Proof. intros; unfold_kort; lia. Qed.

(** Arbeidskorting is nil from € 132.920 on: zero point
    45.592 + 5.685/6,51% = € 132.919,19... *)
Theorem ak_zero : forall w, euro 132919 + 19 <= w -> ak w = 0.
Proof. intros; unfold_kort; lia. Qed.

Theorem ak_pos : forall w, 0 < w <= euro 132919 + 18 -> 0 < ak w.
Proof. intros; unfold_kort; lia. Qed.

(** Maximum € 5.685 is reached exactly on [€ 45.588,61 ; € 45.592]. *)
Theorem ak_plateau : forall w, euro 45588 + 61 <= w <= ak_d_thr -> ak w = sc ak_abc_max.
Proof. intros; unfold_kort; lia. Qed.

(** ** Closed forms per band (used for the marginal-rate analysis).
    All are exact identities, in scaled units. *)
Lemma ak_band_a : forall w, 0 <= w <= ak_b_thr -> ak w = ak_a * w.
Proof. intros; unfold_kort; lia. Qed.

(** The overlap window [€ 11.965, € 11.965,40]: clause a has not yet hit
    its € 996 cap (8,324% x 11.965 = 995,97) while clause b has already
    started, so the arbeidskorting grows at 8,324 + 31,009 = 39,333 %. *)
Lemma ak_band_ab : forall w, ak_b_thr <= w <= euro 11965 + 40 ->
  ak w = ak_a * w + ak_b * (w - ak_b_thr).
Proof. intros; unfold_kort; lia. Qed.

Lemma ak_band_b : forall w, euro 11966 <= w <= euro 25844 ->
  ak w = sc ak_a_max + ak_b * (w - ak_b_thr).
Proof. intros; unfold_kort; lia. Qed.

Lemma ak_band_c : forall w, ak_c_thr <= w <= euro 45588 ->
  ak w = sc ak_ab_max + ak_c * (w - ak_c_thr).
Proof. intros; unfold_kort; lia. Qed.

Lemma ak_band_flat : forall w, euro 45589 <= w <= ak_d_thr -> ak w = sc ak_abc_max.
Proof. intros; unfold_kort; lia. Qed.

Lemma ak_band_d : forall w, ak_d_thr <= w <= euro 132919 + 18 ->
  ak w = sc ak_abc_max - ak_d * (w - ak_d_thr).
Proof. intros; unfold_kort; lia. Qed.

Lemma ahk_band_phase : forall v, ahk_thr <= v <= euro 78423 ->
  ahk v = sc ahk_max - ahk_rate * (v - ahk_thr).
Proof. intros; unfold_kort; lia. Qed.

(** ** Finding: the statute and the Belastingdienst table disagree slightly
    at the arbeidskorting kink € 11.965.  The table says "€ 996 + 31,009% x
    (arbeidsinkomen - € 11.965)" from € 11.965, but by art. 8.11 lid 2
    clause a, 8,324% x 11.965 = € 995,9666, below the € 996 cap. *)
Example ak_at_11965 : ak (euro 11965) = 9959666000.
Proof. vm_compute. reflexivity. Qed.
