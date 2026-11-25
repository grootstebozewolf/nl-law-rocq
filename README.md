# nl-law-rocq: Dutch box-1 income tax 2026, checked in Rocq

A small Rocq formalisation of part of the **Wet inkomstenbelasting 2001**
(Dutch Income Tax Act, BWBR0011353): the box-1 tariff, the national-insurance
premium that is levied with it, and the two main tax credits, as in force on
**1 January 2026**. Every statutory formula is computed exactly and the
properties are machine-checked, with **no `Admitted` and no axioms**.

## The analogy

[Lexifina](https://x.com/mylifcc/status/2125379438607249426) (Alan Yahya)
translated US Internal Revenue Code Title 26 into Lean and "type-checked" the
tax code. The Dutch counterpart of Title 26 is the Wet IB 2001. This project
does the same for a slice of it: write the statute down literally as code,
then *prove* what it does, including the parts the legislator probably did
not intend.

## Scope

| Rule | Article | File |
|---|---|---|
| Box-1 tariff, 3 rows, literal column III base amounts | art. 2.10 lid 1 IB | `Box1.v` |
| Tariff for those born before 1946 (data + floor check) | art. 2.10a | `Params2026.v`, `AOW.v` |
| Premie volksverzekeringen (AOW/Anw/Wlz), capped premie-inkomen | art. 8 lid 3, 10, 11 Wfsv | `Box1.v` |
| Algemene heffingskorting | art. 8.10 lid 2 | `Kortingen.v` |
| Arbeidskorting, clauses a–d | art. 8.11 lid 2, first sentence | `Kortingen.v` |
| Combined credit capped at combined levy (non-refundable) | art. 8.8 (+ 8.1, 8.2) | `Combined.v` |
| Effective marginal rates per band, global step theorem | (derived) | `Marginal.v` |
| AOW-age variant (no AOW premium, credits x 17,85/35,75) | art. 8.3–8.6 IB, art. 10 lid 2 + 12 Wfsv | `AOW.v` |
| Computed examples and Belastingdienst cross-checks | | `Examples.v` |
| `Print Assumptions` audit of 28 main theorems | | `Assumptions.v` |

**The model person** lives in the Netherlands, has wages only, no deductions,
is below AOW age for the whole year (except in `AOW.v`), and claims only the
AHK and the arbeidskorting. Then belastbaar inkomen box 1 = premie-inkomen =
verzamelinkomen = arbeidsinkomen = `y`.

**Arithmetic.** Incomes are integers in eurocents (`Z`). Every statutory
percentage has at most 3 decimals, so it is an integer "per 100 000", and
`rate * cents` is exact in units of 1/100 000 cent. Nothing is rounded except
where the statute itself writes a rounded number (column III of art. 2.10),
plus `/ S` when displaying cents and one floor at 1/100 000 cent in `AOW.v`.

## Parameters (2026) and sources

Statute text: the official consolidated XML of the Wet IB 2001, version
2026-01-01_1
(<https://repository.officiele-overheidspublicaties.nl/bwb/BWBR0011353/2026-01-01_1/xml/BWBR0011353_2026-01-01_1.xml>,
same as <https://wetten.overheid.nl/BWBR0011353/2026-01-01>). The later
2026-02-21 consolidation has the same text for arts. 2.10, 2.10a, 8.8, 8.10
and 8.11. Copies of both statutes' XML are in `sources/`.

| Parameter | Value | Source |
|---|---|---|
| Bracket 1 limit / 2 limit | € 38.883 / € 78.426 | art. 2.10 lid 1 |
| Rates (tax part) | 8,10% / 37,56% / 49,50% | art. 2.10 lid 1 |
| Column III base amounts | € 3.149 / € 18.001 | art. 2.10 lid 1 |
| Born before 1946: limit, col. III | € 41.123; € 3.330 / € 17.341 | art. 2.10a lid 1 |
| AOW / Anw premium | 17,90% / 0,10% | Regeling premiepercentages 2026 (BWBR0051937) art. I, II |
| Wlz premium | 9,65% | Belastingdienst fisin2026 ch. 27 & §21.9.1 |
| Premie-inkomen cap | € 38.883 (= bracket 1 limit) | art. 8 lid 3 Wfsv (BWBR0017745) |
| AHK | € 3.115, minus 6,398% above € 29.736 | art. 8.10 lid 2 |
| AK a | 8,324%, max € 996 | art. 8.11 lid 2 a |
| AK b | 31,009% above € 11.965, a+b ≤ € 5.300 | art. 8.11 lid 2 b |
| AK c | 1,950% above € 25.845, a+b+c ≤ € 5.685 | art. 8.11 lid 2 c |
| AK d | minus 6,51% above € 45.592 | art. 8.11 lid 2 d |

Cross-checked against the Belastingdienst's own 2026 tables (voorlopige
aanslag 2026, AHK table 2026, premie volksverzekeringen page). All of these
agree: combined first-bracket rate 35,75%, maximum premium € 10.751, the
AHK/AK formulas, and the AOW-age first-bracket rate 17,85%.

## Theorems proved (all closed under the global context)

*Sanity*
- `ib_box1_nonneg`, `premie_nonneg`, `levy_nonneg`: no negative tax.
- `premie_max`: premium ≤ 27,65% × € 38.883 (= € 10.751,15).
- `ib_cont_monotone`, `premie_monotone`: the "intended" bracket tax is monotone.
- `ahk_bounds`, `ak_bounds`, `ahk_antitone`, `ahk_full`, `ahk_zero`,
  `ahk_pos_until`, `ak_zero`, `ak_pos`, `ak_plateau`: credit ranges and
  exact zero points. AHK reaches nil at € 78.423,09, a little before the
  € 78.426 used in the Belastingdienst table. AK reaches nil at € 132.919,19.
- `applied_le_levy`, `applied_le_kort`, `applied_nonneg`, `net_nonneg`,
  `net_le_levy`: art. 8.8 as theorems, so there is no negative income tax.
- `cap_binds_low`, `credits_lost_example`, `net_pos_above`: the cap really
  binds. Below € 11.357,84 the net levy is exactly 0 and part of the credits
  is lost (€ 372,40 at € 10.000).

*Marginal rates* (`Marginal.v`: exact slope of the net levy on each band)

| Band (income) | Marginal rate | Composition |
|---|---|---|
| 0 – 11.357,83 | 0% | credits exceed levy (art. 8.8) |
| 11.357,84 – 11.965 | 27,426% | 35,75 − 8,324 |
| **11.965 – 11.965,40** | **−3,583%** | 35,75 − 8,324 − 31,009 |
| 11.966 – 25.844 | 4,741% | 35,75 − 31,009 |
| 25.845 – 29.736 | 33,80% | 35,75 − 1,95 |
| 29.736 – 38.883 | 40,198% | 35,75 + 6,398 − 1,95 |
| 38.883,01 – 45.588 | 42,008% | 37,56 + 6,398 − 1,95 |
| 45.589 – 45.592 | 43,958% | 37,56 + 6,398 |
| **45.592 – 78.423** | **50,468%** | 37,56 + 6,398 + 6,51 |
| 78.423,09 – 78.426 | 44,07% | 37,56 + 6,51 |
| **78.426,01 – 132.919,18** | **56,01%** | 49,50 + 6,51 |
| ≥ 132.919,19 | 49,50% | top rate |

- `mr_B0` … `mr_B10`, `mr_B1b`: the table above, as exact identities
  `net y2 - net y1 = r * (y2 - y1)`.
- `marginal_exceeds_top_rate`: on [€ 45.592, € 78.423] and
  (€ 78.426, € 132.919] the marginal rate is strictly above the 49,50% top rate.
- `step_bounds` (global): for **every** income y ≥ 0 except the three
  exceptions below, one extra cent raises the net levy by between 0 and
  0,5601 cent. The few-euro slivers between bands are checked exhaustively
  by `vm_compute` through a checker proved sound.
- `max_rate_attained`: 56,01% is reached, so it is the maximum.

## Findings (the "type-check finds something" part)

1. **The combined marginal rate exceeds the top rate.** On € 45.592 to
   € 78.423 (still the 37,56% bracket) it is **50,468%**. On € 78.426 to
   € 132.919 it is **56,01%**, the highest rate anywhere in box 1, because the
   arbeidskorting is still being withdrawn at 6,51% after the 49,50% bracket
   starts. An extra € 1 of wages at € 100.000 costs € 0,5601
   (`extra_euro_at_100k`). This is the well-known phase-out effect, now
   proved with exact bands.
2. **The literal tariff of art. 2.10 is not monotone.** Column III (€ 3.149,
   € 18.001) is the continuous amount rounded *down* to whole euros
   (`colIII_2_is_floor`, `colIII_3_is_floor`; same for art. 2.10a). The
   statutory tax is therefore up to € 0,87 below the continuous formula
   (`ib_box1_vs_cont`), and it drops at the bracket edges:
   - going from € 38.883,00 to € 38.883,01 lowers the net levy by **51,88 cents**;
   - going from € 78.426,00 to € 78.426,01 lowers it by **34,52 cents** (`step_at_b1`, `step_at_b2`);
   - in whole euros, € 38.884 pays 10,29 cents less than € 38.883 (`euro_step_b1`).

   `ib_box1_monotone_off_windows` proves these windows (b1 to b1+€1,39,
   b2 to b2+€0,70) are the only ones in the tariff itself.
   Caveat: this is the statute read literally. How the Belastingdienst's
   software rounds in practice was not verified.
3. **A negative marginal rate inside the arbeidskorting.** Clause b starts at
   € 11.965, but clause a only reaches its € 996 cap at € 11.965,40
   (8,324% × 11.965 = € 995,97). For those 40 cents the credit grows at
   39,333%, faster than the 35,75% levy, so the net levy *falls* at
   −3,583% (`mr_B1b`, `step_in_ak_window`). The effect is tiny (1,4 cents in
   total) but real in the statutory text. The Belastingdienst table
   ("€ 996 + 31,009% × (…− € 11.965)") quietly smooths it away, and at
   € 11.965 the statute gives € 995,97 where the table gives € 996
   (`ak_at_11965`).
4. **AOW-age AHK.** By arts. 8.3–8.6 and art. 12 Wfsv, an AOW-age person keeps
   17,85/35,75 of the credit: € 1.555,32 at low income, while the
   Belastingdienst table shows € 1.556 (`ahk_aow_below_published`). The
   phase-out rate 3,195% matches. The Belastingdienst's footnote attributes
   such differences to rounding. For an AOW-age person the top marginal rate
   is 52,75% rather than 56,01% (`aow_step_100k`).

## Simplifications (please read)

- Box 1 only, for one wage earner with no deductions and no partner. Not
  modelled: box 2 and box 3; inkomensafhankelijke combinatiekorting,
  ouderenkorting, alleenstaande-ouderenkorting, jonggehandicaptenkorting;
  art. 2.10 lid 2 (limiting deductions to 37,56%); partner allocation; the
  minimum guarantee in the second sentence of art. 8.11 lid 2 (a wage-tax
  arbeidskorting floor); partial-year residence or partial premium liability;
  the AOW-age arbeidskorting variant beyond the proportional rule.
- The split of credits into IB and premium parts (art. 8.3–8.6) and their
  cross-offset (art. 9 lid 2 Wfsv) is modelled only through the combined
  totals of art. 8.1 b/d and 8.8. That is exact for the combined amount payable.
- The Wlz rate 9,65% is taken from the Belastingdienst pages (it is set by a
  separate VWS regulation that was not fetched). AOW/Anw come from BWBR0051937.
- Box 3 was left out on purpose. Art. 5.2 in the 1-1-2026 consolidation still
  lists 1,44% / 2,61%. The 2026 deemed returns (provisionally 1,28% / 6,00% /
  2,70%) are fixed by ministerial regulation, and in part only after the year
  ends.
- There are no full end-to-end Belastingdienst examples (assessment amounts)
  to compare with. The cross-checks are the published table formulas, the
  maximum premium and the brackets.

## Reproduction

Requires **Rocq 9.2** (developed with The Rocq Prover 9.2, OCaml 5.3.0; any
Rocq 9.x with the bundled Stdlib should work). No other libraries are needed.

```sh
# e.g. via opam:  opam install rocq-prover.9.2.0
# or via docker: docker run --rm -v "$PWD":/w -w /w rocq/rocq-prover:9.2 make
make                # generates Makefile.rocq from _CoqProject and builds theories/
make check-admits   # fails if any Admitted/admit/Axiom/Parameter is present
```

`theories/Assumptions.v` prints `Closed under the global context` for all 28
audited theorems. A clean build takes about 10 s. CI
(`.github/workflows/build.yml`) runs the same steps in the
`rocq/rocq-prover:9.2` container.

## Sources

`sources/` contains unmodified copies of the official consolidated XML of the
Wet inkomstenbelasting 2001 (BWBR0011353, version 2026-01-01_1) and the Wet
financiering sociale verzekeringen (BWBR0017745, version 2026-01-01_0), from
the Dutch government's public repository
<https://repository.officiele-overheidspublicaties.nl/bwb/>. Under art. 11 of
the Dutch Auteurswet (Copyright Act), statutes are not subject to copyright.

## License

Copyright (c) 2026 Jeroen Bloemscheer.

Licensed under the **European Union Public Licence v. 1.2 (EUPL-1.2)**; see
[`LICENSE`](LICENSE) (official English text, SPDX identifier `EUPL-1.2`).
The statute texts in `sources/` are public-domain government publications and
are not covered by this licence.
