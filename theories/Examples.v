(** * Concrete computed examples (vm_compute), amounts in CENTS (floored).

    Model person: below AOW age, wages only, no deductions, AHK + AK only.
    "net" = box-1 income tax + premie volksverzekeringen - credits (art. 8.8). *)
From Stdlib Require Import ZArith.
From NLLaw Require Import Params2026 Box1 Kortingen Combined AOW.
Open Scope Z_scope.

Definition cents (x : Z) : Z := x / S.

(** ** Cross-checks against figures published by the Belastingdienst
    (https://www.belastingdienst.nl/wps/wcm/connect/nl/voorlopige-aanslag/content/voorlopige-aanslag-tarieven-en-heffingskortingen ,
     https://www.belastingdienst.nl/wps/wcm/connect/bldcontentnl/belastingdienst/prive/werk_en_inkomen/sociale_verzekeringen/premies_volks_en_werknemersverzekeringen/volksverzekeringen/hoeveel_moet_u_betalen ). *)

(* "Maximum te betalen [premie volksverzekeringen 2026]: € 10.751" *)
Example bd_max_premie : cents (premie (euro 200000)) = 1075114.
Proof. vm_compute. reflexivity. Qed.

(* AHK table: € 3.115 up to € 29.736 *)
Example bd_ahk_29736 : cents (ahk (euro 29736)) = 311500.
Proof. vm_compute. reflexivity. Qed.

(* AHK table: € 3.115 - 6,398% x (50.000 - 29.736) = € 1.818,5088 *)
Example bd_ahk_50000 : cents (ahk (euro 50000)) = 181850.
Proof. vm_compute. reflexivity. Qed.

(* AK table: € 5.300 at € 25.845, € 5.685 at € 45.592 *)
Example bd_ak_25845 : cents (ak (euro 25845)) = 530000.
Proof. vm_compute. reflexivity. Qed.
Example bd_ak_45592 : cents (ak (euro 45592)) = 568500.
Proof. vm_compute. reflexivity. Qed.

(* AK table: € 5.685 - 6,510% x (60.000 - 45.592) = € 4.747,0392 *)
Example bd_ak_60000 : cents (ak (euro 60000)) = 474703.
Proof. vm_compute. reflexivity. Qed.

(* Box-1 combined first-bracket rate 35,75% (table "tot en met € 38.883  35,75%") *)
Example bd_levy_38883 : levy (euro 38883) = 35750 * euro 38883.
Proof. vm_compute. reflexivity. Qed.

(** ** Net levy at selected incomes (below AOW age)
      income      levy      AHK      AK     credits    NET     NET(AOW-age) *)
Example net_10k  : cents (net (euro 10000))  = 0.        Proof. vm_compute. reflexivity. Qed.
Example net_20k  : cents (net (euro 20000))  = 54742.    Proof. vm_compute. reflexivity. Qed.
Example net_30k  : cents (net (euro 30000))  = 224586.   Proof. vm_compute. reflexivity. Qed.
Example net_40k  : cents (net (euro 40000))  = 628536.   Proof. vm_compute. reflexivity. Qed.
Example net_50k  : cents (net (euro 50000))  = 1085914.  Proof. vm_compute. reflexivity. Qed.
Example net_60k  : cents (net (euro 60000))  = 1590594.  Proof. vm_compute. reflexivity. Qed.
Example net_80k  : cents (net (euro 80000))  = 2608624.  Proof. vm_compute. reflexivity. Qed.
Example net_100k : cents (net (euro 100000)) = 3728824.  Proof. vm_compute. reflexivity. Qed.
Example net_150k : cents (net (euro 150000)) = 6418127.  Proof. vm_compute. reflexivity. Qed.

(* Credits lost to the art. 8.8 cap at € 10.000: credits € 3.947,40, levy € 3.575. *)
Example lost_10k : cents (kort (euro 10000) - applied (euro 10000)) = 37240.
Proof. vm_compute. reflexivity. Qed.

(* Same incomes, AOW age the whole year (no ouderenkorting modelled). *)
Example net_aow_20k  : cents (net_aow (euro 20000))  = 27333.   Proof. vm_compute. reflexivity. Qed.
Example net_aow_50k  : cents (net_aow (euro 50000))  = 751240.  Proof. vm_compute. reflexivity. Qed.
Example net_aow_100k : cents (net_aow (euro 100000)) = 3140120. Proof. vm_compute. reflexivity. Qed.
