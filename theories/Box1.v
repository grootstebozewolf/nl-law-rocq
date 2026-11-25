(** * Box 1: tax on taxable income from work and home (art. 2.10 Wet IB 2001)
      and the premie volksverzekeringen (art. 8-10 Wfsv). *)
From Stdlib Require Import ZArith Lia.
From NLLaw Require Import Params2026.
Open Scope Z_scope.

(** Taxable income is never negative in our model; we clamp. *)
Definition clamp0 (y : Z) : Z := Z.max 0 y.

(** ** Art. 2.10 lid 1, read LITERALLY: base amount from column III plus the
    column IV percentage of the excess over column I.  Rows are selected by
    "meer dan [I] maar niet meer dan [II]".  Result in scaled units. *)
Definition ib_box1 (y0 : Z) : Z :=
  let y := clamp0 y0 in
  if y <=? b1 then r_ib1 * y
  else if y <=? b2 then sc colIII_2 + r_ib2 * (y - b1)
  else sc colIII_3 + r_ib3 * (y - b2).

(** The "intended" continuous bracket tax, i.e. each rate applied to the
    slice of income in its bracket, without the rounded column-III amounts. *)
Definition ib_cont (y0 : Z) : Z :=
  let y := clamp0 y0 in
  r_ib1 * Z.min y b1
  + r_ib2 * Z.max 0 (Z.min y b2 - b1)
  + r_ib3 * Z.max 0 (y - b2).

(** ** Premie volksverzekeringen: art. 10 lid 1 Wfsv on premie-inkomen
    capped at b1 (art. 8 lid 3 Wfsv).  Person below AOW age. *)
Definition premie (y0 : Z) : Z := r_prem * Z.min (clamp0 y0) b1.

(** Gross combined levy on box 1 (art. 8.1 lid 1 onder b, box-1 part only). *)
Definition levy (y : Z) : Z := ib_box1 y + premie y.
Definition levy_cont (y : Z) : Z := ib_cont y + premie y.

Ltac unfold_box1 :=
  unfold levy, levy_cont, ib_box1, ib_cont, premie, clamp0,
         b1, b2, colIII_2, colIII_3, r_ib1, r_ib2, r_ib3,
         r_prem, r_aow, r_anw, r_wlz, sc, S, euro in *.

Ltac split_ifs :=
  repeat match goal with
  | |- context [if ?a <=? ?b then _ else _] => destruct (Z.leb_spec a b)
  end.

(** ** Basic sanity theorems *)

Theorem ib_box1_nonneg : forall y, 0 <= ib_box1 y.
Proof. intros; unfold_box1; cbv zeta; split_ifs; lia. Qed.

Theorem premie_nonneg : forall y, 0 <= premie y.
Proof. intros; unfold_box1; lia. Qed.

Theorem levy_nonneg : forall y, 0 <= levy y.
Proof. intros; pose proof (ib_box1_nonneg y); pose proof (premie_nonneg y);
       unfold levy; lia. Qed.

(** The premium never exceeds 27,65% of € 38.883 (= € 10.751,15; the
    Belastingdienst publishes "maximum te betalen € 10.751"). *)
Theorem premie_max : forall y, premie y <= r_prem * b1.
Proof. intros; unfold_box1; lia. Qed.

Example premie_max_value : r_prem * b1 = 107511495000. (* € 10.751,14950 *)
Proof. reflexivity. Qed.

(** The continuous bracket tax is monotone (each slice has a positive rate). *)
Theorem ib_cont_monotone : forall y1 y2, y1 <= y2 -> ib_cont y1 <= ib_cont y2.
Proof. intros; unfold_box1; cbv zeta; lia. Qed.

Theorem premie_monotone : forall y1 y2, y1 <= y2 -> premie y1 <= premie y2.
Proof. intros; unfold_box1; lia. Qed.

(** ** Finding 1: column III of art. 2.10 is the continuous amount ROUNDED
    DOWN to whole euros.  8,10% x 38.883 = 3.149,523 and
    3.149 + 37,56% x 39.543 = 18.001,3508. *)
Theorem colIII_2_is_floor :
  sc colIII_2 <= ib_cont b1 < sc colIII_2 + sc (euro 1).
Proof. unfold_box1; cbv zeta; lia. Qed.

Theorem colIII_3_is_floor :
  sc colIII_3 <= sc colIII_2 + r_ib2 * (b2 - b1) < sc colIII_3 + sc (euro 1).
Proof. unfold_box1; lia. Qed.

(** Consequently the literal statutory tax is never above the continuous
    one, and at most 87,38 cents below it. *)
Theorem ib_box1_vs_cont : forall y,
  ib_box1 y <= ib_cont y /\ ib_cont y - ib_box1 y <= 8738000.
Proof. intros; unfold_box1; cbv zeta; split_ifs; lia. Qed.

(** ... and therefore the literal statutory tariff is NOT monotone:
    earning € 38.884 instead of € 38.883 lowers the box-1 tax
    (€ 3.149,3756 < € 3.149,5230), and likewise one cent above € 78.426. *)
Theorem ib_box1_not_monotone_b1 :
  ib_box1 (euro 38884) < ib_box1 (euro 38883).
Proof. vm_compute. reflexivity. Qed.

Theorem ib_box1_not_monotone_b2 :
  ib_box1 (euro 78426 + 1) < ib_box1 (euro 78426).
Proof. vm_compute. reflexivity. Qed.

Theorem levy_not_monotone :
  levy (euro 38884) < levy (euro 38883).
Proof. vm_compute. reflexivity. Qed.

(** Exact size of the dips (in scaled units = 1/100000 cent):
    -14,74 cent at b1 and -34,585 cent at b2 + 1 cent. *)
Example dip_b1 : ib_box1 (euro 38884) - ib_box1 (euro 38883) = -1474000.
Proof. vm_compute. reflexivity. Qed.
Example dip_b2 : ib_box1 (euro 78426 + 1) - ib_box1 (euro 78426) = -3458500.
Proof. vm_compute. reflexivity. Qed.

(** Where exactly is monotonicity violated?  Only in two short windows just
    above each bracket boundary: from b1 to b1 + € 1,39 and from b2 to
    b2 + € 0,70.  Outside those windows the literal tariff is monotone. *)
Theorem ib_box1_monotone_off_windows : forall y1 y2,
  0 <= y1 <= y2 ->
  (y2 <= b1 \/ b1 + 140 <= y2 \/ y1 > b1) ->
  (y2 <= b2 \/ b2 + 71 <= y2 \/ y1 > b2) ->
  ib_box1 y1 <= ib_box1 y2.
Proof. intros; unfold_box1; cbv zeta; split_ifs; lia. Qed.
