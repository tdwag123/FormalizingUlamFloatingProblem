"""Propose rational certificates and emit Lean proofs that check them.

Floating-point computations select candidate values only. They have no role in
the trusted proof: every emitted numerical inequality is proved by Lean's exact
arithmetic, using the kernel-checked Taylor enclosure lemmas.
"""

from fractions import Fraction as Q
from pathlib import Path
import math
import argparse

ROOT = Path(__file__).resolve().parents[1]
AL = Q(4487989505, 10**10)
AU = Q(4487989506, 10**10)
PIL = Q(31415926535, 10**10)
PIU = Q(31415926536, 10**10)


def real(x):
    x = Q(x)
    return f"(({x.numerator} : ℝ) / {x.denominator})"


def enclosure(value, scale=10**8):
    return Q(math.floor(value * scale) - 1, scale), Q(math.ceil(value * scale) + 1, scale)


SINES = {k: enclosure(math.sin(k * math.pi / 7)) for k in (1, 2, 3)}
COSES = {k: enclosure(math.cos(k * math.pi / 7)) for k in (1, 2, 3)}
COTS = {
    k: (Q(math.floor(COSES[k][0] / SINES[k][1] * 10**7) - 1, 10**7),
        Q(math.ceil(COSES[k][1] / SINES[k][0] * 10**7) + 1, 10**7))
    for k in (1, 2, 3)
}


def trig_proof(kind, x, lo, hi):
    return (f"{kind}_rational_enclosure (x := {real(x)}) (L := {real(lo)}) (U := {real(hi)})\n"
            f"    (by norm_num) (by norm_num [{kind}Polynomial14]) (by norm_num [{kind}Polynomial14])")


def emit_globals():
    out = ["import Seventh.RationalTrig\nimport Seventh.FrequencyResidues\n",
           "/-! Exact global enclosures. Generated candidates; all proofs are checked by Lean. -/\n",
           "namespace UlamFloating.Seventh\n",
           f"theorem certificate_pi_bounds : {real(PIL)} ≤ Real.pi ∧ Real.pi ≤ {real(PIU)} := by\n"
           "  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]\n",
           f"theorem certificate_angle_bounds : {real(AL)} ≤ Real.pi / 7 ∧ Real.pi / 7 ≤ {real(AU)} := by\n"
           "  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]\n"]
    for k in (1, 2, 3):
        x = f"({k} * (Real.pi / 7))"
        for kind, table in (("sin", SINES), ("cos", COSES)):
            lo, hi = table[k]
            out.append(f"theorem certificate_{kind}_{k} : {real(lo)} ≤ Real.{kind} {x} ∧ "
                       f"Real.{kind} {x} ≤ {real(hi)} := by\n"
                       f"  have hL := {trig_proof(kind, k*AL, lo, hi)}\n"
                       f"  have hU := {trig_proof(kind, k*AU, lo, hi)}\n"
                       f"  have hxL : {real(k*AL)} ≤ {x} := by linarith [certificate_angle_bounds.1]\n"
                       f"  have hxU : {x} ≤ {real(k*AU)} := by linarith [certificate_angle_bounds.2]\n")
            if kind == "sin":
                out.append(f"  have hmL := Real.sin_le_sin_of_le_of_le_pi_div_two\n"
                           f"    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ {real(k*AL)})\n"
                           f"    (by linarith [Real.pi_pos] : {x} ≤ Real.pi / 2) hxL\n"
                           f"  have hmU := Real.sin_le_sin_of_le_of_le_pi_div_two\n"
                           f"    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ {x})\n"
                           f"    (by linarith [Real.pi_gt_d2] : {real(k*AU)} ≤ Real.pi / 2) hxU\n"
                           "  exact ⟨hL.1.trans hmL, hmU.trans hU.2⟩\n")
            else:
                out.append(f"  have hmL := Real.cos_le_cos_of_nonneg_of_le_pi\n"
                           f"    (by norm_num : 0 ≤ {real(k*AL)})\n"
                           f"    (by linarith [Real.pi_pos] : {x} ≤ Real.pi) hxL\n"
                           f"  have hmU := Real.cos_le_cos_of_nonneg_of_le_pi\n"
                           f"    (by positivity : 0 ≤ {x})\n"
                           f"    (by linarith [Real.pi_gt_d2] : {real(k*AU)} ≤ Real.pi) hxU\n"
                           "  exact ⟨hU.1.trans hmU, hmL.trans hL.2⟩\n")
        lo, hi = COTS[k]
        out.append(f"theorem certificate_cot_{k} : {real(lo)} ≤ Real.cot {x} ∧ Real.cot {x} ≤ {real(hi)} := by\n"
                   f"  have hs := certificate_sin_{k}\n"
                   f"  have hc := certificate_cos_{k}\n"
                   f"  have hpos : 0 < Real.sin {x} := by linarith [hs.1]\n"
                   "  rw [Real.cot_eq_cos_div_sin]\n"
                   "  constructor\n"
                   "  · apply (le_div_iff₀ hpos).mpr\n"
                   "    nlinarith only [hs.2, hc.1]\n"
                   "  · apply (div_le_iff₀ hpos).mpr\n"
                   "    nlinarith only [hs.1, hc.2]\n")
    out.append("end UlamFloating.Seventh\n")
    path = ROOT / "Seventh" / "GlobalNumerics.lean"
    path.write_text("\n".join(out), encoding="utf-8")
    print(f"Emitted {path.name}; Lean validation is required.")


def ceil_grid(x):
    return Q(math.ceil(x * 10**6) + 1, 10**6)


def candidate(j):
    lo, hi = Q(j, 10000), Q(j+1, 10000)
    B = Q(math.floor(math.acos(float(hi)/(math.pi/7))*10**6)-1, 10**6)
    sb = enclosure(math.sin(float(B)))
    cb = enclosure(math.cos(float(B)))
    J = ceil_grid(2*(SINES[1][1]-lo)/sb[0])
    low, high = math.pi/7, 1.2
    for _ in range(65):
        mid = (low+high)/2
        if math.sin(mid) > 2*math.cos(mid/2+2*float(B)):
            high = mid
        else:
            low = mid
    UN = ceil_grid(high)
    UP = ceil_grid(float(AU)+(float(3*PIU*J/lo))**(1/3))
    peak = UP < UN
    U = min(UN, UP)
    su = enclosure(math.sin(float(U)))
    cn = enclosure(math.cos(float(U/2+2*B)))
    pminus = (su[0]-SINES[1][1])/(U-AL)
    pplus = (SINES[1][1]-sb[0])/(AL-B)
    c = Q(round((pminus+pplus)/2*10**6), 10**6)
    w = ceil_grid(max(c-pminus,pplus-c))
    gap = min(c, c-hi*2*COTS[2][1], c-hi*3*COTS[3][1],
              lo*8*COTS[1][0]-c, lo*9*COTS[2][0]-c, lo*10*COTS[3][0]-c)
    delta = Q(math.floor(gap*10**6)-1, 10**6)
    V = ceil_grid(min(J,(AU-B)*(U-AL)))
    contraction = (w/delta)**2+SINES[1][1]**2/2*(1/SINES[1][0]**2+(w/(7*lo))**2)**2*V
    if not contraction < Q(19,20):
        raise ValueError(f"Candidate contraction failed at {j}: {float(contraction)}")
    return dict(j=j,lo=lo,hi=hi,B=B,U=U,c=c,w=w,delta=delta,J=J,V=V,
                sb=sb,su=su,cb=cb,cn=cn,peak=peak,contraction=contraction)


def emit_cell(d):
    j=d['j']; B=d['B']; U=d['U']; lo=d['lo']; J=d['J']; V=d['V']
    args=' '.join(real(d[k]) for k in ('lo','hi','B','U','c','w','delta','J','V'))
    s=[f"set_option maxHeartbeats 1000000 in\ntheorem cell_{j} : CellCertificate {args} := by\n",
       "  have hA := certificate_angle_bounds\n  have hS := certificate_sin_1\n"
       "  simp only [one_mul] at hS\n",
       f"  have hSB := {trig_proof('sin',B,*d['sb'])}\n",
       f"  have hSU := {trig_proof('sin',U,*d['su'])}\n",
       f"  have hCB := {trig_proof('cos',B,*d['cb'])}\n"]
    if not d['peak']:
        s.append(f"  have hCN := {trig_proof('cos',U/2+2*B,*d['cn'])}\n")
    s.append("  refine {\n"
             "    frequency_pos := by norm_num\n    lower_pos := by norm_num\n"
             "    lower_lt_mean := by linarith only [hA.1]\n"
             "    mean_lt_upper := by linarith only [hA.2]\n"
             "    upper_le := by norm_num\n    width_nonneg := by norm_num\n"
             "    gap_pos := by norm_num\n    variance_nonneg := by norm_num\n"
             "    projection := ?_\n    jensen := ?_\n    angle_upper := ?_\n"
             "    variance := ?_\n    approximation_lower := ?_\n    approximation_upper := ?_\n"
             "    gap_center := by norm_num\n    gap_two := ?_\n    gap_three := ?_\n"
             "    gap_eight := ?_\n    gap_nine := ?_\n    gap_ten := ?_\n    contraction := ?_ }\n"
             "  · have hp := mul_le_mul hA.1 hCB.1 (by norm_num) (by positivity : 0 ≤ Real.pi / 7)\n"
             "    exact lt_of_lt_of_le (by norm_num) hp\n"
             "  · nlinarith only [hS.2, hSB.1]\n")
    if d['peak']:
        s.append("  · right\n"
                 "    calc\n"
                 f"      3 * Real.pi * {real(J)} ≤ 3 * {real(PIU)} * {real(J)} := by\n"
                 "        nlinarith only [certificate_pi_bounds.2]\n"
                 f"      _ < {real(lo)} * ({real(U)} - {real(AU)}) ^ 3 := by norm_num\n"
                 f"      _ ≤ {real(lo)} * ({real(U)} - Real.pi / 7) ^ 3 := by\n"
                 "        apply mul_le_mul_of_nonneg_left _ (by norm_num)\n"
                 "        apply pow_le_pow_left₀ (by norm_num)\n"
                 "        linarith only [hA.2]\n")
    else:
        s.append("  · left\n    norm_num at hCN ⊢\n    nlinarith only [hCN.2, hSU.1]\n")
    if J <= V:
        s.append("  · left\n    norm_num\n")
    else:
        s.append("  · right\n"
                 f"    have hp := mul_le_mul (sub_le_sub_right hA.2 {real(B)})\n"
                 f"      (sub_le_sub_left hA.1 {real(U)}) (by linarith only [hA.2]) (by norm_num)\n"
                 "    exact hp.trans (by norm_num)\n")
    s.append("  · nlinarith only [hA.1, hS.2, hSU.1]\n"
             "  · nlinarith only [hA.1, hS.2, hSB.1]\n")
    for n,k,side in [(2,2,2),(3,3,2),(8,1,1),(9,2,1),(10,3,1)]:
        s.append(f"  · have ht := certificate_cot_{k}\n"
                 f"    unfold seventhMultiplier\n    rw [cot_frequency_residue ({n} : ℤ)]\n"
                 f"    norm_num at ht ⊢\n    nlinarith only [ht.{side}]\n")
    s.append("  · apply certificate_contraction_of_rational (by norm_num) (by norm_num)\n"
             "    norm_num\n")
    return ''.join(s)


def emit_cells(count):
    data=[candidate(j) for j in range(4200,4200+count)]
    for block,start in enumerate(range(0,count,10)):
        dependency='Seventh.NumericalComparison' if block==0 else f'Seventh.Cells{block-1}'
        text=f'import {dependency}\n\n/-! Rational cell certificates, verified by Lean. -/\n\nnamespace UlamFloating.Seventh\n\n'
        text+='\n'.join(emit_cell(d) for d in data[start:start+10])
        text+='\nend UlamFloating.Seventh\n'
        (ROOT/'Seventh'/f'Cells{block}.lean').write_text(text,encoding='utf-8')
    print(f'Emitted {count} cell candidates; largest rational contraction {float(max(d["contraction"] for d in data)):.10f}.')
    print('The emitted Lean proofs must compile before these are accepted as certificates.')
    if count == 139:
        text=('import Seventh.Cells13\n\nnamespace UlamFloating.Seventh\n\n'
              'set_option maxHeartbeats 1000000 in\n'
              '/-- A checked certificate for every cell in the entire frequency range. -/\n'
              'theorem certificate_for_index (j : ℕ) (hlo : 4200 ≤ j) (hhi : j ≤ 4338) :\n'
              '    ∃ B U c w δ J V : ℝ,\n'
              '      CellCertificate ((j : ℝ) / 10000) (((j + 1 : ℕ) : ℝ) / 10000) B U c w δ J V := by\n'
              '  interval_cases j\n')
        for d in data:
            args=', '.join(real(d[k]) for k in ('B','U','c','w','delta','J','V'))
            text+=f'  · refine ⟨{args}, ?_⟩\n    convert cell_{d["j"]} using 1 <;> norm_num\n'
        text+='\nend UlamFloating.Seventh\n'
        (ROOT/'Seventh'/'AllCells.lean').write_text(text,encoding='utf-8')


if __name__ == "__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument('--cells',type=int,default=0,choices=range(0,140))
    args=parser.parse_args()
    emit_globals()
    if args.cells:
        emit_cells(args.cells)
