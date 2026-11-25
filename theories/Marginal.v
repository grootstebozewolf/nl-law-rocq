(** * Effective marginal rates of the combined box-1 levy net of AHK + AK.

    The marginal rate on a band is the exact slope of [net]: on band k,
    [net y2 - net y1 = r_k * (y2 - y1)] where r_k is "per 100 000"
    (e.g. 56010 = 56,010 %).  All bands are in cents; together with the
    finitely many one-cent steps that are checked by computation, they cover
    every income y >= 0. *)
From Stdlib Require Import ZArith Lia.
From NLLaw Require Import Params2026 Box1 Kortingen Combined.
Open Scope Z_scope.

Ltac nums :=
  unfold r_comb, b1, b2, colIII_2, colIII_3, r_ib1, r_ib2, r_ib3, r_prem, r_aow,
    r_anw, r_wlz, ahk_max, ahk_thr, ahk_rate, ak_a, ak_a_max, ak_b,
    ak_b_thr, ak_ab_max, ak_c, ak_c_thr, ak_abc_max, ak_d, ak_d_thr,
    sc, S, euro in *.

Ltac rw_forms y :=
  first [ rewrite (levy_r1 y) by (nums; lia)
        | rewrite (levy_r2 y) by (nums; lia)
        | rewrite (levy_r3 y) by (nums; lia) ];
  first [ rewrite (ahk_full y) by (nums; lia)
        | rewrite (ahk_band_phase y) by (nums; lia)
        | rewrite (ahk_zero y) by (nums; lia) ];
  first [ rewrite (ak_band_a y) by (nums; lia)
        | rewrite (ak_band_ab y) by (nums; lia)
        | rewrite (ak_band_b y) by (nums; lia)
        | rewrite (ak_band_c y) by (nums; lia)
        | rewrite (ak_band_flat y) by (nums; lia)
        | rewrite (ak_band_d y) by (nums; lia)
        | rewrite (ak_zero y) by (nums; lia) ].

Ltac solve_band :=
  let y1 := fresh "y1" in let y2 := fresh "y2" in
  intros y1 y2 ? ?;
  rewrite (net_slack y1) by (unfold kort; rw_forms y1; nums; lia);
  rewrite (net_slack y2) by (unfold kort; rw_forms y2; nums; lia);
  unfold kort; rw_forms y1; rw_forms y2; nums; lia.

(** Band 0: [0, € 11.357,83] -- credits exceed the levy, net = 0 (art. 8.8). *)
Theorem mr_B0 : forall y1 y2, 0 <= y1 <= y2 -> y2 <= euro 11357 + 83 ->
  net y2 - net y1 = 0 * (y2 - y1).
Proof. intros. rewrite !cap_binds_low by lia. lia. Qed.

(** Band 1: [€ 11.357,84, € 11.965]: 35,75 - 8,324 = 27,426 %. *)
Theorem mr_B1 : forall y1 y2, euro 11357 + 84 <= y1 <= y2 -> y2 <= euro 11965 ->
  net y2 - net y1 = 27426 * (y2 - y1).
Proof. solve_band. Qed.

(** Band 1b: [€ 11.965, € 11.965,40]: 35,75 - 8,324 - 31,009 = -3,583 %.
    A NEGATIVE marginal rate: the arbeidskorting grows faster (39,333 %)
    than the levy (35,75 %), because the statutory € 996 cap of clause a is
    reached only at € 11.965,40, 40 cents after clause b starts.  The
    Belastingdienst table ("€ 996 + 31,009% x (arbeidsinkomen - € 11.965)")
    does not have this window. *)
Theorem mr_B1b : forall y1 y2, euro 11965 <= y1 <= y2 -> y2 <= euro 11965 + 40 ->
  net y2 - net y1 = -3583 * (y2 - y1).
Proof. solve_band. Qed.

(** Band 2: [€ 11.966, € 25.844]: 35,75 - 31,009 = 4,741 %. *)
Theorem mr_B2 : forall y1 y2, euro 11966 <= y1 <= y2 -> y2 <= euro 25844 ->
  net y2 - net y1 = 4741 * (y2 - y1).
Proof. solve_band. Qed.

(** Band 3: [€ 25.845, € 29.736]: 35,75 - 1,95 = 33,80 %. *)
Theorem mr_B3 : forall y1 y2, euro 25845 <= y1 <= y2 -> y2 <= euro 29736 ->
  net y2 - net y1 = 33800 * (y2 - y1).
Proof. solve_band. Qed.

(** Band 4: [€ 29.736, € 38.883]: 35,75 + 6,398 - 1,95 = 40,198 %. *)
Theorem mr_B4 : forall y1 y2, euro 29736 <= y1 <= y2 -> y2 <= euro 38883 ->
  net y2 - net y1 = 40198 * (y2 - y1).
Proof. solve_band. Qed.

(** Band 5: (€ 38.883, € 45.588]: 37,56 + 6,398 - 1,95 = 42,008 %. *)
Theorem mr_B5 : forall y1 y2, euro 38883 + 1 <= y1 <= y2 -> y2 <= euro 45588 ->
  net y2 - net y1 = 42008 * (y2 - y1).
Proof. solve_band. Qed.

(** Band 6: [€ 45.589, € 45.592] (AK at its € 5.685 plateau): 37,56 + 6,398 = 43,958 %. *)
Theorem mr_B6 : forall y1 y2, euro 45589 <= y1 <= y2 -> y2 <= euro 45592 ->
  net y2 - net y1 = 43958 * (y2 - y1).
Proof. solve_band. Qed.

(** Band 7: [€ 45.592, € 78.423]: 37,56 + 6,398 + 6,51 = 50,468 %
    -- ABOVE the 49,50 % top rate, while still in the 37,56 % bracket. *)
Theorem mr_B7 : forall y1 y2, euro 45592 <= y1 <= y2 -> y2 <= euro 78423 ->
  net y2 - net y1 = 50468 * (y2 - y1).
Proof. solve_band. Qed.

(** Band 8: [€ 78.423,09, € 78.426] (AHK exhausted): 37,56 + 6,51 = 44,07 %. *)
Theorem mr_B8 : forall y1 y2, euro 78423 + 9 <= y1 <= y2 -> y2 <= euro 78426 ->
  net y2 - net y1 = 44070 * (y2 - y1).
Proof. solve_band. Qed.

(** Band 9: (€ 78.426, € 132.919,18]: 49,50 + 6,51 = 56,01 %
    -- the highest marginal rate anywhere. *)
Theorem mr_B9 : forall y1 y2, euro 78426 + 1 <= y1 <= y2 -> y2 <= euro 132919 + 18 ->
  net y2 - net y1 = 56010 * (y2 - y1).
Proof. solve_band. Qed.

(** Band 10: from € 132.919,19: the plain top rate 49,50 %. *)
Theorem mr_B10 : forall y1 y2, euro 132919 + 19 <= y1 -> y1 <= y2 ->
  net y2 - net y1 = 49500 * (y2 - y1).
Proof. solve_band. Qed.

(** ** Headline finding: the combined marginal rate exceeds the top
    statutory rate (49,50 %) on two bands totalling about € 87.300 of income:
    50,468 % on [€ 45.592, € 78.423] and 56,01 % on (€ 78.426, € 132.919]. *)
Theorem marginal_exceeds_top_rate :
  (forall y1 y2, euro 45592 <= y1 < y2 -> y2 <= euro 78423 ->
     net y2 - net y1 > r_ib3 * (y2 - y1)) /\
  (forall y1 y2, euro 78426 + 1 <= y1 < y2 -> y2 <= euro 132919 + 18 ->
     net y2 - net y1 > r_ib3 * (y2 - y1)).
Proof.
  split; intros y1 y2 H1 H2.
  - rewrite (mr_B7 y1 y2) by lia. unfold r_ib3; lia.
  - rewrite (mr_B9 y1 y2) by lia. unfold r_ib3; lia.
Qed.

(** An extra euro of wages at € 100.000 costs 56,01 cents. *)
Example extra_euro_at_100k : net (euro 100001) - net (euro 100000) = 56010 * 100.
Proof. vm_compute. reflexivity. Qed.

(** ** Global one-cent step theorem.
    For EVERY income y >= 0 except
      - y = € 38.883 and y = € 78.426 (rounded column-III amounts of
        art. 2.10: one more cent LOWERS the levy by 51,88 resp. 34,52 cent),
      - y in [€ 11.965,00, € 11.965,39] (arbeidskorting overlap window:
        each extra cent lowers the levy by 0,03583 cent),
    one extra cent raises the net levy by between 0 and 0,5601 cent. *)

Definition step (y : Z) : Z := net (y + 1) - net y.

Definition step_ok (y : Z) : bool := (0 <=? step y) && (step y <=? 56010).

Fixpoint check_range (lo : Z) (n : nat) : bool :=
  match n with
  | O => true
  | Datatypes.S n' => step_ok lo && check_range (lo + 1) n'
  end.

Lemma check_range_sound : forall n lo, check_range lo n = true ->
  forall y, lo <= y < lo + Z.of_nat n -> step_ok y = true.
Proof.
  induction n as [|n IH]; intros lo Hc y Hy; simpl in *.
  - lia.
  - apply andb_prop in Hc as [H1 H2].
    destruct (Z.eq_dec y lo) as [->|Hne]; [exact H1|].
    apply (IH (lo + 1)); [exact H2|lia].
Qed.

Lemma step_ok_spec : forall y, step_ok y = true -> 0 <= step y <= 56010.
Proof. intros y H; unfold step_ok in H; apply andb_prop in H as [H1 H2]; lia. Qed.

(* The transition slivers between bands, checked exhaustively by computation. *)
Lemma gap1 : check_range (euro 11357 + 83) 1 = true.   Proof. vm_compute; reflexivity. Qed.
Lemma gap2 : check_range (euro 11965 + 40) 60 = true.     Proof. vm_compute; reflexivity. Qed.
Lemma gap3 : check_range (euro 25844) 100 = true.      Proof. vm_compute; reflexivity. Qed.
Lemma gap4 : check_range (euro 45588) 100 = true.      Proof. vm_compute; reflexivity. Qed.
Lemma gap5 : check_range (euro 78423) 9 = true.        Proof. vm_compute; reflexivity. Qed.
Lemma gap6 : check_range (euro 132919 + 18) 1 = true.  Proof. vm_compute; reflexivity. Qed.

Theorem step_bounds : forall y, 0 <= y -> y <> b1 -> y <> b2 ->
  ~ (ak_b_thr <= y < ak_b_thr + 40) ->
  0 <= step y <= 56010.
Proof.
  intros y Hy Hb1 Hb2 Hw. unfold b1, b2, ak_b_thr, euro in Hb1, Hb2, Hw.
  assert (G : forall lo n, check_range lo n = true -> lo <= y < lo + Z.of_nat n ->
                0 <= step y <= 56010)
    by (intros lo n Hc Hr; apply step_ok_spec; exact (check_range_sound n lo Hc y Hr)).
  unfold step.
  destruct (Z_lt_le_dec y (euro 11357 + 83)) as [h0|h0].
  { rewrite (mr_B0 y (y+1)) by (unfold euro in *; lia). lia. }
  destruct (Z.eq_dec y (euro 11357 + 83)) as [e|e].
  { apply (G _ _ gap1). unfold euro in *; simpl; lia. }
  destruct (Z_lt_le_dec y (euro 11965)) as [h1|h1].
  { rewrite (mr_B1 y (y+1)) by (unfold euro in *; lia). lia. }
  destruct (Z_lt_le_dec y (euro 11965 + 40)) as [hw|hw].
  { exfalso; unfold euro in *; lia. }
  destruct (Z_lt_le_dec y (euro 11966)) as [h2|h2].
  { apply (G _ _ gap2). simpl; unfold euro in *; lia. }
  destruct (Z_lt_le_dec y (euro 25844)) as [h3|h3].
  { rewrite (mr_B2 y (y+1)) by (unfold euro in *; lia). lia. }
  destruct (Z_lt_le_dec y (euro 25845)) as [h4|h4].
  { apply (G _ _ gap3). simpl; unfold euro in *; lia. }
  destruct (Z_lt_le_dec y (euro 29736)) as [h5|h5].
  { rewrite (mr_B3 y (y+1)) by (unfold euro in *; lia). lia. }
  destruct (Z_lt_le_dec y (euro 38883)) as [h6|h6].
  { rewrite (mr_B4 y (y+1)) by (unfold euro in *; lia). lia. }
  destruct (Z_lt_le_dec y (euro 45588)) as [h7|h7].
  { rewrite (mr_B5 y (y+1)) by (unfold euro in *; lia). lia. }
  destruct (Z_lt_le_dec y (euro 45589)) as [h8|h8].
  { apply (G _ _ gap4). simpl; unfold euro in *; lia. }
  destruct (Z_lt_le_dec y (euro 45592)) as [h9|h9].
  { rewrite (mr_B6 y (y+1)) by (unfold euro in *; lia). lia. }
  destruct (Z_lt_le_dec y (euro 78423)) as [h10|h10].
  { rewrite (mr_B7 y (y+1)) by (unfold euro in *; lia). lia. }
  destruct (Z_lt_le_dec y (euro 78423 + 9)) as [h11|h11].
  { apply (G _ _ gap5). simpl; unfold euro in *; lia. }
  destruct (Z_lt_le_dec y (euro 78426)) as [h12|h12].
  { rewrite (mr_B8 y (y+1)) by (unfold euro in *; lia). lia. }
  destruct (Z_lt_le_dec y (euro 132919 + 18)) as [h13|h13].
  { rewrite (mr_B9 y (y+1)) by (unfold euro in *; lia). lia. }
  destruct (Z.eq_dec y (euro 132919 + 18)) as [e2|e2].
  { apply (G _ _ gap6). unfold euro in *; simpl; lia. }
  rewrite (mr_B10 y (y+1)) by (unfold euro in *; lia). lia.
Qed.

(** The two exceptional points: one more cent, less tax. *)
Example step_at_b1 : step b1 = -5187992.  (* -51,88 cent *)
Proof. vm_compute. reflexivity. Qed.
Example step_at_b2 : step b2 = -3451990.  (* -34,52 cent *)
Proof. vm_compute. reflexivity. Qed.

Theorem step_in_ak_window : forall y, ak_b_thr <= y < ak_b_thr + 40 ->
  step y = -3583.
Proof.
  intros y Hy. unfold step. unfold ak_b_thr, euro in Hy.
  rewrite (mr_B1b y (y+1)) by (unfold euro; lia). lia.
Qed.

Theorem net_not_monotone : net (b1 + 1) < net b1 /\ net (b2 + 1) < net b2.
Proof. vm_compute. split; reflexivity. Qed.

(** In whole euros the anomaly survives at b1 only: € 38.884 pays about
    10 cents less than € 38.883. *)
Example euro_step_b1 : net (euro 38884) - net (euro 38883) = -1029200. (* -10,292 cent *)
Proof. vm_compute. reflexivity. Qed.

Theorem max_rate_attained : exists y, 0 <= y /\ step y = 56010.
Proof. exists (euro 100000). split; [unfold euro; lia|vm_compute; reflexivity]. Qed.
