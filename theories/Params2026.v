(** * Statutory parameters, Dutch income tax (Wet IB 2001), tax year 2026

    Every number below is copied from the consolidated text of the
    Wet inkomstenbelasting 2001 (BWBR0011353) as in force on 1 January 2026
    (official XML: https://repository.officiele-overheidspublicaties.nl/bwb/BWBR0011353/2026-01-01_1/xml/BWBR0011353_2026-01-01_1.xml ,
     human-readable: https://wetten.overheid.nl/BWBR0011353/2026-01-01 ;
     a copy is in sources/), or from the 2026 premium-rate regulation /
     Belastingdienst where the IB 2001 delegates to the Wfsv.

    Units.
    - Incomes are integers in eurocents ([Z]).
    - Statutory percentages all have at most three decimals, so a rate is an
      integer "per 100 000" (e.g. 35,75 % = 35750).
    - Hence [rate * cents] is an amount in "scaled units" = 1/100000 cent,
      and every statutory formula is computed EXACTLY, with no rounding,
      in scaled units.  [sc] lifts cents to scaled units. *)

From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition S : Z := 100000.            (* denominator of a rate *)
Definition euro (e : Z) : Z := e * 100. (* euros -> cents *)
Definition sc (c : Z) : Z := c * S.     (* cents -> scaled units *)

(** ** Art. 2.10 lid 1 Wet IB 2001 (tarief box 1), version 1-1-2026.
    Table: I = "meer dan", II = "maar niet meer dan", III = base amount,
    IV = percentage.
      -        | € 38.883 | –        | 8,10%
      € 38.883 | € 78.426 | € 3.149  | 37,56%
      € 78.426 | –        | € 18.001 | 49,50%
    NB: the first-bracket 8,10% is the TAX part only; the premie
    volksverzekeringen (Wfsv) comes on top, see below. *)
Definition b1        : Z := euro 38883.  (* art. 2.10 lid 1, col. II row 1 *)
Definition b2        : Z := euro 78426.  (* art. 2.10 lid 1, col. II row 2 *)
Definition colIII_2  : Z := euro 3149.   (* art. 2.10 lid 1, col. III row 2 *)
Definition colIII_3  : Z := euro 18001.  (* art. 2.10 lid 1, col. III row 3 *)
Definition r_ib1     : Z := 8100.        (* 8,10%  art. 2.10 lid 1 row 1 *)
Definition r_ib2     : Z := 37560.       (* 37,56% art. 2.10 lid 1 row 2 *)
Definition r_ib3     : Z := 49500.       (* 49,50% art. 2.10 lid 1 row 3 *)

(** ** Art. 2.10a lid 1 (born before 1 January 1946), version 1-1-2026.
      -        | € 41.123 | –        | 8,10%
      € 41.123 | € 78.426 | € 3.330  | 37,56%
      € 78.426 | –        | € 17.341 | 49,50%  *)
Definition b1_pre46       : Z := euro 41123.
Definition colIII_2_pre46 : Z := euro 3330.
Definition colIII_3_pre46 : Z := euro 17341.

(** ** Premie volksverzekeringen (Wet financiering sociale verzekeringen,
    BWBR0017745, 2026-01-01).
    - Art. 10 Wfsv: premie = sum of the art. 11 percentages x premie-inkomen;
      art. 10 lid 2: no AOW premium from AOW age.
    - Art. 8 lid 3 Wfsv: premie-inkomen capped at the first col. II amount of
      art. 2.10 IB (i.e. b1 = € 38.883).
    - Rates 2026: AOW 17,90% and Anw 0,10%: Regeling premiepercentages ...
      2026 (BWBR0051937), art. I and II,
      https://wetten.overheid.nl/BWBR0051937/2026-01-01/0 ;
      Wlz 9,65%: Belastingdienst,
      https://www.belastingdienst.nl/wps/wcm/connect/fisin/fisin2026/premie_volksverzekeringen
      (also section 21.9.1 of .../fisin2026/heffingskortingen:
       "belastingdeel 8,10% ... AOW 17,90%, Anw 0,10%, Wlz 9,65%. In totaal 35,75%").
      Belastingdienst states the 2026 maximum premium as € 10.751. *)
Definition r_aow : Z := 17900.
Definition r_anw : Z := 100.
Definition r_wlz : Z := 9650.
Definition r_prem : Z := r_aow + r_anw + r_wlz.  (* 27,65% *)

(** Art. 8.1 lid 1 onder c: gecombineerd heffingspercentage = 8,10 + 27,65. *)
Definition r_comb : Z := r_ib1 + r_prem.          (* 35,75% *)

(** ** Art. 8.10 lid 2 (algemene heffingskorting), 2026:
    "€ 3.115, verminderd, doch niet verder dan tot nihil, met 6,398% van het
     gedeelte van het verzamelinkomen dat meer bedraagt dan € 29.736." *)
Definition ahk_max  : Z := euro 3115.
Definition ahk_thr  : Z := euro 29736.
Definition ahk_rate : Z := 6398.

(** ** Art. 8.11 lid 2 (arbeidskorting), 2026:
    a. 8,324% of arbeidsinkomen, max € 996; plus
    b. 31,009% of the part above € 11.965, a+b at most € 5.300; plus
    c. 1,950% of the part above € 25.845, a+b+c at most € 5.685;
    minus (not below nil)
    d. 6,51% of the part above € 45.592. *)
Definition ak_a       : Z := 8324.
Definition ak_a_max   : Z := euro 996.
Definition ak_b       : Z := 31009.
Definition ak_b_thr   : Z := euro 11965.
Definition ak_ab_max  : Z := euro 5300.
Definition ak_c       : Z := 1950.
Definition ak_c_thr   : Z := euro 25845.
Definition ak_abc_max : Z := euro 5685.
Definition ak_d       : Z := 6510.
Definition ak_d_thr   : Z := euro 45592.
