/-!
# Performance calibration workload (`scripts/perf-budgets.py`, docs/perf-budgets.md)

Pure Lean, no imports beyond `Init`: elaboration and kernel checking of a fixed mix of `omega`,
`simp`, `decide` and `decide +kernel` goals. Its wall time is the machine's unit: the normalized
gate compares proof time as a multiple of this file's time measured in the same run, so a
slower or faster machine cancels. Do not edit it casually: the budgets file records its SHA-256,
and a change needs a rebaseline.
-/
set_option maxRecDepth 4000


theorem omega_1 (a b c d : Nat) (h1 : a + 1 < b) (h2 : b * 2 < c + 3) (h3 : c < d + 1) :
    a + 1 < d + 4 + b := by omega

theorem omega_2 (a b c d : Nat) (h1 : a + 2 < b) (h2 : b * 2 < c + 6) (h3 : c < d + 2) :
    a + 2 < d + 8 + b := by omega

theorem omega_3 (a b c d : Nat) (h1 : a + 3 < b) (h2 : b * 2 < c + 9) (h3 : c < d + 3) :
    a + 3 < d + 12 + b := by omega

theorem omega_4 (a b c d : Nat) (h1 : a + 4 < b) (h2 : b * 2 < c + 12) (h3 : c < d + 4) :
    a + 4 < d + 16 + b := by omega

theorem omega_5 (a b c d : Nat) (h1 : a + 5 < b) (h2 : b * 2 < c + 15) (h3 : c < d + 5) :
    a + 5 < d + 20 + b := by omega

theorem omega_6 (a b c d : Nat) (h1 : a + 6 < b) (h2 : b * 2 < c + 18) (h3 : c < d + 6) :
    a + 6 < d + 24 + b := by omega

theorem omega_7 (a b c d : Nat) (h1 : a + 7 < b) (h2 : b * 2 < c + 21) (h3 : c < d + 7) :
    a + 7 < d + 28 + b := by omega

theorem omega_8 (a b c d : Nat) (h1 : a + 8 < b) (h2 : b * 2 < c + 24) (h3 : c < d + 8) :
    a + 8 < d + 32 + b := by omega

theorem omega_9 (a b c d : Nat) (h1 : a + 9 < b) (h2 : b * 2 < c + 27) (h3 : c < d + 9) :
    a + 9 < d + 36 + b := by omega

theorem omega_10 (a b c d : Nat) (h1 : a + 10 < b) (h2 : b * 2 < c + 30) (h3 : c < d + 10) :
    a + 10 < d + 40 + b := by omega

theorem omega_11 (a b c d : Nat) (h1 : a + 11 < b) (h2 : b * 2 < c + 33) (h3 : c < d + 11) :
    a + 11 < d + 44 + b := by omega

theorem omega_12 (a b c d : Nat) (h1 : a + 12 < b) (h2 : b * 2 < c + 36) (h3 : c < d + 12) :
    a + 12 < d + 48 + b := by omega

theorem omega_13 (a b c d : Nat) (h1 : a + 13 < b) (h2 : b * 2 < c + 39) (h3 : c < d + 13) :
    a + 13 < d + 52 + b := by omega

theorem omega_14 (a b c d : Nat) (h1 : a + 14 < b) (h2 : b * 2 < c + 42) (h3 : c < d + 14) :
    a + 14 < d + 56 + b := by omega

theorem omega_15 (a b c d : Nat) (h1 : a + 15 < b) (h2 : b * 2 < c + 45) (h3 : c < d + 15) :
    a + 15 < d + 60 + b := by omega

theorem omega_16 (a b c d : Nat) (h1 : a + 16 < b) (h2 : b * 2 < c + 48) (h3 : c < d + 16) :
    a + 16 < d + 64 + b := by omega

theorem omega_17 (a b c d : Nat) (h1 : a + 17 < b) (h2 : b * 2 < c + 51) (h3 : c < d + 17) :
    a + 17 < d + 68 + b := by omega

theorem omega_18 (a b c d : Nat) (h1 : a + 18 < b) (h2 : b * 2 < c + 54) (h3 : c < d + 18) :
    a + 18 < d + 72 + b := by omega

theorem omega_19 (a b c d : Nat) (h1 : a + 19 < b) (h2 : b * 2 < c + 57) (h3 : c < d + 19) :
    a + 19 < d + 76 + b := by omega

theorem omega_20 (a b c d : Nat) (h1 : a + 20 < b) (h2 : b * 2 < c + 60) (h3 : c < d + 20) :
    a + 20 < d + 80 + b := by omega

theorem omega_21 (a b c d : Nat) (h1 : a + 21 < b) (h2 : b * 2 < c + 63) (h3 : c < d + 21) :
    a + 21 < d + 84 + b := by omega

theorem omega_22 (a b c d : Nat) (h1 : a + 22 < b) (h2 : b * 2 < c + 66) (h3 : c < d + 22) :
    a + 22 < d + 88 + b := by omega

theorem omega_23 (a b c d : Nat) (h1 : a + 23 < b) (h2 : b * 2 < c + 69) (h3 : c < d + 23) :
    a + 23 < d + 92 + b := by omega

theorem omega_24 (a b c d : Nat) (h1 : a + 24 < b) (h2 : b * 2 < c + 72) (h3 : c < d + 24) :
    a + 24 < d + 96 + b := by omega

theorem omega_25 (a b c d : Nat) (h1 : a + 25 < b) (h2 : b * 2 < c + 75) (h3 : c < d + 25) :
    a + 25 < d + 100 + b := by omega

theorem omega_26 (a b c d : Nat) (h1 : a + 26 < b) (h2 : b * 2 < c + 78) (h3 : c < d + 26) :
    a + 26 < d + 104 + b := by omega

theorem omega_27 (a b c d : Nat) (h1 : a + 27 < b) (h2 : b * 2 < c + 81) (h3 : c < d + 27) :
    a + 27 < d + 108 + b := by omega

theorem omega_28 (a b c d : Nat) (h1 : a + 28 < b) (h2 : b * 2 < c + 84) (h3 : c < d + 28) :
    a + 28 < d + 112 + b := by omega

theorem omega_29 (a b c d : Nat) (h1 : a + 29 < b) (h2 : b * 2 < c + 87) (h3 : c < d + 29) :
    a + 29 < d + 116 + b := by omega

theorem omega_30 (a b c d : Nat) (h1 : a + 30 < b) (h2 : b * 2 < c + 90) (h3 : c < d + 30) :
    a + 30 < d + 120 + b := by omega

theorem omega_31 (a b c d : Nat) (h1 : a + 31 < b) (h2 : b * 2 < c + 93) (h3 : c < d + 31) :
    a + 31 < d + 124 + b := by omega

theorem omega_32 (a b c d : Nat) (h1 : a + 32 < b) (h2 : b * 2 < c + 96) (h3 : c < d + 32) :
    a + 32 < d + 128 + b := by omega

theorem omega_33 (a b c d : Nat) (h1 : a + 33 < b) (h2 : b * 2 < c + 99) (h3 : c < d + 33) :
    a + 33 < d + 132 + b := by omega

theorem omega_34 (a b c d : Nat) (h1 : a + 34 < b) (h2 : b * 2 < c + 102) (h3 : c < d + 34) :
    a + 34 < d + 136 + b := by omega

theorem omega_35 (a b c d : Nat) (h1 : a + 35 < b) (h2 : b * 2 < c + 105) (h3 : c < d + 35) :
    a + 35 < d + 140 + b := by omega

theorem omega_36 (a b c d : Nat) (h1 : a + 36 < b) (h2 : b * 2 < c + 108) (h3 : c < d + 36) :
    a + 36 < d + 144 + b := by omega

theorem omega_37 (a b c d : Nat) (h1 : a + 37 < b) (h2 : b * 2 < c + 111) (h3 : c < d + 37) :
    a + 37 < d + 148 + b := by omega

theorem omega_38 (a b c d : Nat) (h1 : a + 38 < b) (h2 : b * 2 < c + 114) (h3 : c < d + 38) :
    a + 38 < d + 152 + b := by omega

theorem omega_39 (a b c d : Nat) (h1 : a + 39 < b) (h2 : b * 2 < c + 117) (h3 : c < d + 39) :
    a + 39 < d + 156 + b := by omega

theorem omega_40 (a b c d : Nat) (h1 : a + 40 < b) (h2 : b * 2 < c + 120) (h3 : c < d + 40) :
    a + 40 < d + 160 + b := by omega

theorem omega_41 (a b c d : Nat) (h1 : a + 41 < b) (h2 : b * 2 < c + 123) (h3 : c < d + 41) :
    a + 41 < d + 164 + b := by omega

theorem omega_42 (a b c d : Nat) (h1 : a + 42 < b) (h2 : b * 2 < c + 126) (h3 : c < d + 42) :
    a + 42 < d + 168 + b := by omega

theorem omega_43 (a b c d : Nat) (h1 : a + 43 < b) (h2 : b * 2 < c + 129) (h3 : c < d + 43) :
    a + 43 < d + 172 + b := by omega

theorem omega_44 (a b c d : Nat) (h1 : a + 44 < b) (h2 : b * 2 < c + 132) (h3 : c < d + 44) :
    a + 44 < d + 176 + b := by omega

theorem omega_45 (a b c d : Nat) (h1 : a + 45 < b) (h2 : b * 2 < c + 135) (h3 : c < d + 45) :
    a + 45 < d + 180 + b := by omega

theorem omega_46 (a b c d : Nat) (h1 : a + 46 < b) (h2 : b * 2 < c + 138) (h3 : c < d + 46) :
    a + 46 < d + 184 + b := by omega

theorem omega_47 (a b c d : Nat) (h1 : a + 47 < b) (h2 : b * 2 < c + 141) (h3 : c < d + 47) :
    a + 47 < d + 188 + b := by omega

theorem omega_48 (a b c d : Nat) (h1 : a + 48 < b) (h2 : b * 2 < c + 144) (h3 : c < d + 48) :
    a + 48 < d + 192 + b := by omega

theorem omega_49 (a b c d : Nat) (h1 : a + 49 < b) (h2 : b * 2 < c + 147) (h3 : c < d + 49) :
    a + 49 < d + 196 + b := by omega

theorem omega_50 (a b c d : Nat) (h1 : a + 50 < b) (h2 : b * 2 < c + 150) (h3 : c < d + 50) :
    a + 50 < d + 200 + b := by omega

theorem omega_51 (a b c d : Nat) (h1 : a + 51 < b) (h2 : b * 2 < c + 153) (h3 : c < d + 51) :
    a + 51 < d + 204 + b := by omega

theorem omega_52 (a b c d : Nat) (h1 : a + 52 < b) (h2 : b * 2 < c + 156) (h3 : c < d + 52) :
    a + 52 < d + 208 + b := by omega

theorem omega_53 (a b c d : Nat) (h1 : a + 53 < b) (h2 : b * 2 < c + 159) (h3 : c < d + 53) :
    a + 53 < d + 212 + b := by omega

theorem omega_54 (a b c d : Nat) (h1 : a + 54 < b) (h2 : b * 2 < c + 162) (h3 : c < d + 54) :
    a + 54 < d + 216 + b := by omega

theorem omega_55 (a b c d : Nat) (h1 : a + 55 < b) (h2 : b * 2 < c + 165) (h3 : c < d + 55) :
    a + 55 < d + 220 + b := by omega

theorem omega_56 (a b c d : Nat) (h1 : a + 56 < b) (h2 : b * 2 < c + 168) (h3 : c < d + 56) :
    a + 56 < d + 224 + b := by omega

theorem omega_57 (a b c d : Nat) (h1 : a + 57 < b) (h2 : b * 2 < c + 171) (h3 : c < d + 57) :
    a + 57 < d + 228 + b := by omega

theorem omega_58 (a b c d : Nat) (h1 : a + 58 < b) (h2 : b * 2 < c + 174) (h3 : c < d + 58) :
    a + 58 < d + 232 + b := by omega

theorem omega_59 (a b c d : Nat) (h1 : a + 59 < b) (h2 : b * 2 < c + 177) (h3 : c < d + 59) :
    a + 59 < d + 236 + b := by omega

theorem omega_60 (a b c d : Nat) (h1 : a + 60 < b) (h2 : b * 2 < c + 180) (h3 : c < d + 60) :
    a + 60 < d + 240 + b := by omega

theorem omega_61 (a b c d : Nat) (h1 : a + 61 < b) (h2 : b * 2 < c + 183) (h3 : c < d + 61) :
    a + 61 < d + 244 + b := by omega

theorem omega_62 (a b c d : Nat) (h1 : a + 62 < b) (h2 : b * 2 < c + 186) (h3 : c < d + 62) :
    a + 62 < d + 248 + b := by omega

theorem omega_63 (a b c d : Nat) (h1 : a + 63 < b) (h2 : b * 2 < c + 189) (h3 : c < d + 63) :
    a + 63 < d + 252 + b := by omega

theorem omega_64 (a b c d : Nat) (h1 : a + 64 < b) (h2 : b * 2 < c + 192) (h3 : c < d + 64) :
    a + 64 < d + 256 + b := by omega

theorem omega_65 (a b c d : Nat) (h1 : a + 65 < b) (h2 : b * 2 < c + 195) (h3 : c < d + 65) :
    a + 65 < d + 260 + b := by omega

theorem omega_66 (a b c d : Nat) (h1 : a + 66 < b) (h2 : b * 2 < c + 198) (h3 : c < d + 66) :
    a + 66 < d + 264 + b := by omega

theorem omega_67 (a b c d : Nat) (h1 : a + 67 < b) (h2 : b * 2 < c + 201) (h3 : c < d + 67) :
    a + 67 < d + 268 + b := by omega

theorem omega_68 (a b c d : Nat) (h1 : a + 68 < b) (h2 : b * 2 < c + 204) (h3 : c < d + 68) :
    a + 68 < d + 272 + b := by omega

theorem omega_69 (a b c d : Nat) (h1 : a + 69 < b) (h2 : b * 2 < c + 207) (h3 : c < d + 69) :
    a + 69 < d + 276 + b := by omega

theorem omega_70 (a b c d : Nat) (h1 : a + 70 < b) (h2 : b * 2 < c + 210) (h3 : c < d + 70) :
    a + 70 < d + 280 + b := by omega

theorem omega_71 (a b c d : Nat) (h1 : a + 71 < b) (h2 : b * 2 < c + 213) (h3 : c < d + 71) :
    a + 71 < d + 284 + b := by omega

theorem omega_72 (a b c d : Nat) (h1 : a + 72 < b) (h2 : b * 2 < c + 216) (h3 : c < d + 72) :
    a + 72 < d + 288 + b := by omega

theorem omega_73 (a b c d : Nat) (h1 : a + 73 < b) (h2 : b * 2 < c + 219) (h3 : c < d + 73) :
    a + 73 < d + 292 + b := by omega

theorem omega_74 (a b c d : Nat) (h1 : a + 74 < b) (h2 : b * 2 < c + 222) (h3 : c < d + 74) :
    a + 74 < d + 296 + b := by omega

theorem omega_75 (a b c d : Nat) (h1 : a + 75 < b) (h2 : b * 2 < c + 225) (h3 : c < d + 75) :
    a + 75 < d + 300 + b := by omega

theorem omega_76 (a b c d : Nat) (h1 : a + 76 < b) (h2 : b * 2 < c + 228) (h3 : c < d + 76) :
    a + 76 < d + 304 + b := by omega

theorem omega_77 (a b c d : Nat) (h1 : a + 77 < b) (h2 : b * 2 < c + 231) (h3 : c < d + 77) :
    a + 77 < d + 308 + b := by omega

theorem omega_78 (a b c d : Nat) (h1 : a + 78 < b) (h2 : b * 2 < c + 234) (h3 : c < d + 78) :
    a + 78 < d + 312 + b := by omega

theorem omega_79 (a b c d : Nat) (h1 : a + 79 < b) (h2 : b * 2 < c + 237) (h3 : c < d + 79) :
    a + 79 < d + 316 + b := by omega

theorem omega_80 (a b c d : Nat) (h1 : a + 80 < b) (h2 : b * 2 < c + 240) (h3 : c < d + 80) :
    a + 80 < d + 320 + b := by omega

theorem omega_81 (a b c d : Nat) (h1 : a + 81 < b) (h2 : b * 2 < c + 243) (h3 : c < d + 81) :
    a + 81 < d + 324 + b := by omega

theorem omega_82 (a b c d : Nat) (h1 : a + 82 < b) (h2 : b * 2 < c + 246) (h3 : c < d + 82) :
    a + 82 < d + 328 + b := by omega

theorem omega_83 (a b c d : Nat) (h1 : a + 83 < b) (h2 : b * 2 < c + 249) (h3 : c < d + 83) :
    a + 83 < d + 332 + b := by omega

theorem omega_84 (a b c d : Nat) (h1 : a + 84 < b) (h2 : b * 2 < c + 252) (h3 : c < d + 84) :
    a + 84 < d + 336 + b := by omega

theorem omega_85 (a b c d : Nat) (h1 : a + 85 < b) (h2 : b * 2 < c + 255) (h3 : c < d + 85) :
    a + 85 < d + 340 + b := by omega

theorem omega_86 (a b c d : Nat) (h1 : a + 86 < b) (h2 : b * 2 < c + 258) (h3 : c < d + 86) :
    a + 86 < d + 344 + b := by omega

theorem omega_87 (a b c d : Nat) (h1 : a + 87 < b) (h2 : b * 2 < c + 261) (h3 : c < d + 87) :
    a + 87 < d + 348 + b := by omega

theorem omega_88 (a b c d : Nat) (h1 : a + 88 < b) (h2 : b * 2 < c + 264) (h3 : c < d + 88) :
    a + 88 < d + 352 + b := by omega

theorem omega_89 (a b c d : Nat) (h1 : a + 89 < b) (h2 : b * 2 < c + 267) (h3 : c < d + 89) :
    a + 89 < d + 356 + b := by omega

theorem omega_90 (a b c d : Nat) (h1 : a + 90 < b) (h2 : b * 2 < c + 270) (h3 : c < d + 90) :
    a + 90 < d + 360 + b := by omega

theorem omega_91 (a b c d : Nat) (h1 : a + 91 < b) (h2 : b * 2 < c + 273) (h3 : c < d + 91) :
    a + 91 < d + 364 + b := by omega

theorem omega_92 (a b c d : Nat) (h1 : a + 92 < b) (h2 : b * 2 < c + 276) (h3 : c < d + 92) :
    a + 92 < d + 368 + b := by omega

theorem omega_93 (a b c d : Nat) (h1 : a + 93 < b) (h2 : b * 2 < c + 279) (h3 : c < d + 93) :
    a + 93 < d + 372 + b := by omega

theorem omega_94 (a b c d : Nat) (h1 : a + 94 < b) (h2 : b * 2 < c + 282) (h3 : c < d + 94) :
    a + 94 < d + 376 + b := by omega

theorem omega_95 (a b c d : Nat) (h1 : a + 95 < b) (h2 : b * 2 < c + 285) (h3 : c < d + 95) :
    a + 95 < d + 380 + b := by omega

theorem omega_96 (a b c d : Nat) (h1 : a + 96 < b) (h2 : b * 2 < c + 288) (h3 : c < d + 96) :
    a + 96 < d + 384 + b := by omega

theorem omega_97 (a b c d : Nat) (h1 : a + 97 < b) (h2 : b * 2 < c + 291) (h3 : c < d + 97) :
    a + 97 < d + 388 + b := by omega

theorem omega_98 (a b c d : Nat) (h1 : a + 98 < b) (h2 : b * 2 < c + 294) (h3 : c < d + 98) :
    a + 98 < d + 392 + b := by omega

theorem omega_99 (a b c d : Nat) (h1 : a + 99 < b) (h2 : b * 2 < c + 297) (h3 : c < d + 99) :
    a + 99 < d + 396 + b := by omega

theorem omega_100 (a b c d : Nat) (h1 : a + 100 < b) (h2 : b * 2 < c + 300) (h3 : c < d + 100) :
    a + 100 < d + 400 + b := by omega

theorem omega_101 (a b c d : Nat) (h1 : a + 101 < b) (h2 : b * 2 < c + 303) (h3 : c < d + 101) :
    a + 101 < d + 404 + b := by omega

theorem omega_102 (a b c d : Nat) (h1 : a + 102 < b) (h2 : b * 2 < c + 306) (h3 : c < d + 102) :
    a + 102 < d + 408 + b := by omega

theorem omega_103 (a b c d : Nat) (h1 : a + 103 < b) (h2 : b * 2 < c + 309) (h3 : c < d + 103) :
    a + 103 < d + 412 + b := by omega

theorem omega_104 (a b c d : Nat) (h1 : a + 104 < b) (h2 : b * 2 < c + 312) (h3 : c < d + 104) :
    a + 104 < d + 416 + b := by omega

theorem omega_105 (a b c d : Nat) (h1 : a + 105 < b) (h2 : b * 2 < c + 315) (h3 : c < d + 105) :
    a + 105 < d + 420 + b := by omega

theorem omega_106 (a b c d : Nat) (h1 : a + 106 < b) (h2 : b * 2 < c + 318) (h3 : c < d + 106) :
    a + 106 < d + 424 + b := by omega

theorem omega_107 (a b c d : Nat) (h1 : a + 107 < b) (h2 : b * 2 < c + 321) (h3 : c < d + 107) :
    a + 107 < d + 428 + b := by omega

theorem omega_108 (a b c d : Nat) (h1 : a + 108 < b) (h2 : b * 2 < c + 324) (h3 : c < d + 108) :
    a + 108 < d + 432 + b := by omega

theorem omega_109 (a b c d : Nat) (h1 : a + 109 < b) (h2 : b * 2 < c + 327) (h3 : c < d + 109) :
    a + 109 < d + 436 + b := by omega

theorem omega_110 (a b c d : Nat) (h1 : a + 110 < b) (h2 : b * 2 < c + 330) (h3 : c < d + 110) :
    a + 110 < d + 440 + b := by omega

theorem omega_111 (a b c d : Nat) (h1 : a + 111 < b) (h2 : b * 2 < c + 333) (h3 : c < d + 111) :
    a + 111 < d + 444 + b := by omega

theorem omega_112 (a b c d : Nat) (h1 : a + 112 < b) (h2 : b * 2 < c + 336) (h3 : c < d + 112) :
    a + 112 < d + 448 + b := by omega

theorem omega_113 (a b c d : Nat) (h1 : a + 113 < b) (h2 : b * 2 < c + 339) (h3 : c < d + 113) :
    a + 113 < d + 452 + b := by omega

theorem omega_114 (a b c d : Nat) (h1 : a + 114 < b) (h2 : b * 2 < c + 342) (h3 : c < d + 114) :
    a + 114 < d + 456 + b := by omega

theorem omega_115 (a b c d : Nat) (h1 : a + 115 < b) (h2 : b * 2 < c + 345) (h3 : c < d + 115) :
    a + 115 < d + 460 + b := by omega

theorem omega_116 (a b c d : Nat) (h1 : a + 116 < b) (h2 : b * 2 < c + 348) (h3 : c < d + 116) :
    a + 116 < d + 464 + b := by omega

theorem omega_117 (a b c d : Nat) (h1 : a + 117 < b) (h2 : b * 2 < c + 351) (h3 : c < d + 117) :
    a + 117 < d + 468 + b := by omega

theorem omega_118 (a b c d : Nat) (h1 : a + 118 < b) (h2 : b * 2 < c + 354) (h3 : c < d + 118) :
    a + 118 < d + 472 + b := by omega

theorem omega_119 (a b c d : Nat) (h1 : a + 119 < b) (h2 : b * 2 < c + 357) (h3 : c < d + 119) :
    a + 119 < d + 476 + b := by omega

theorem omega_120 (a b c d : Nat) (h1 : a + 120 < b) (h2 : b * 2 < c + 360) (h3 : c < d + 120) :
    a + 120 < d + 480 + b := by omega

theorem omega_121 (a b c d : Nat) (h1 : a + 121 < b) (h2 : b * 2 < c + 363) (h3 : c < d + 121) :
    a + 121 < d + 484 + b := by omega

theorem omega_122 (a b c d : Nat) (h1 : a + 122 < b) (h2 : b * 2 < c + 366) (h3 : c < d + 122) :
    a + 122 < d + 488 + b := by omega

theorem omega_123 (a b c d : Nat) (h1 : a + 123 < b) (h2 : b * 2 < c + 369) (h3 : c < d + 123) :
    a + 123 < d + 492 + b := by omega

theorem omega_124 (a b c d : Nat) (h1 : a + 124 < b) (h2 : b * 2 < c + 372) (h3 : c < d + 124) :
    a + 124 < d + 496 + b := by omega

theorem omega_125 (a b c d : Nat) (h1 : a + 125 < b) (h2 : b * 2 < c + 375) (h3 : c < d + 125) :
    a + 125 < d + 500 + b := by omega

theorem omega_126 (a b c d : Nat) (h1 : a + 126 < b) (h2 : b * 2 < c + 378) (h3 : c < d + 126) :
    a + 126 < d + 504 + b := by omega

theorem omega_127 (a b c d : Nat) (h1 : a + 127 < b) (h2 : b * 2 < c + 381) (h3 : c < d + 127) :
    a + 127 < d + 508 + b := by omega

theorem omega_128 (a b c d : Nat) (h1 : a + 128 < b) (h2 : b * 2 < c + 384) (h3 : c < d + 128) :
    a + 128 < d + 512 + b := by omega

theorem omega_129 (a b c d : Nat) (h1 : a + 129 < b) (h2 : b * 2 < c + 387) (h3 : c < d + 129) :
    a + 129 < d + 516 + b := by omega

theorem omega_130 (a b c d : Nat) (h1 : a + 130 < b) (h2 : b * 2 < c + 390) (h3 : c < d + 130) :
    a + 130 < d + 520 + b := by omega

theorem omega_131 (a b c d : Nat) (h1 : a + 131 < b) (h2 : b * 2 < c + 393) (h3 : c < d + 131) :
    a + 131 < d + 524 + b := by omega

theorem omega_132 (a b c d : Nat) (h1 : a + 132 < b) (h2 : b * 2 < c + 396) (h3 : c < d + 132) :
    a + 132 < d + 528 + b := by omega

theorem omega_133 (a b c d : Nat) (h1 : a + 133 < b) (h2 : b * 2 < c + 399) (h3 : c < d + 133) :
    a + 133 < d + 532 + b := by omega

theorem omega_134 (a b c d : Nat) (h1 : a + 134 < b) (h2 : b * 2 < c + 402) (h3 : c < d + 134) :
    a + 134 < d + 536 + b := by omega

theorem omega_135 (a b c d : Nat) (h1 : a + 135 < b) (h2 : b * 2 < c + 405) (h3 : c < d + 135) :
    a + 135 < d + 540 + b := by omega

theorem omega_136 (a b c d : Nat) (h1 : a + 136 < b) (h2 : b * 2 < c + 408) (h3 : c < d + 136) :
    a + 136 < d + 544 + b := by omega

theorem omega_137 (a b c d : Nat) (h1 : a + 137 < b) (h2 : b * 2 < c + 411) (h3 : c < d + 137) :
    a + 137 < d + 548 + b := by omega

theorem omega_138 (a b c d : Nat) (h1 : a + 138 < b) (h2 : b * 2 < c + 414) (h3 : c < d + 138) :
    a + 138 < d + 552 + b := by omega

theorem omega_139 (a b c d : Nat) (h1 : a + 139 < b) (h2 : b * 2 < c + 417) (h3 : c < d + 139) :
    a + 139 < d + 556 + b := by omega

theorem omega_140 (a b c d : Nat) (h1 : a + 140 < b) (h2 : b * 2 < c + 420) (h3 : c < d + 140) :
    a + 140 < d + 560 + b := by omega

theorem omega_141 (a b c d : Nat) (h1 : a + 141 < b) (h2 : b * 2 < c + 423) (h3 : c < d + 141) :
    a + 141 < d + 564 + b := by omega

theorem omega_142 (a b c d : Nat) (h1 : a + 142 < b) (h2 : b * 2 < c + 426) (h3 : c < d + 142) :
    a + 142 < d + 568 + b := by omega

theorem omega_143 (a b c d : Nat) (h1 : a + 143 < b) (h2 : b * 2 < c + 429) (h3 : c < d + 143) :
    a + 143 < d + 572 + b := by omega

theorem omega_144 (a b c d : Nat) (h1 : a + 144 < b) (h2 : b * 2 < c + 432) (h3 : c < d + 144) :
    a + 144 < d + 576 + b := by omega

theorem omega_145 (a b c d : Nat) (h1 : a + 145 < b) (h2 : b * 2 < c + 435) (h3 : c < d + 145) :
    a + 145 < d + 580 + b := by omega

theorem omega_146 (a b c d : Nat) (h1 : a + 146 < b) (h2 : b * 2 < c + 438) (h3 : c < d + 146) :
    a + 146 < d + 584 + b := by omega

theorem omega_147 (a b c d : Nat) (h1 : a + 147 < b) (h2 : b * 2 < c + 441) (h3 : c < d + 147) :
    a + 147 < d + 588 + b := by omega

theorem omega_148 (a b c d : Nat) (h1 : a + 148 < b) (h2 : b * 2 < c + 444) (h3 : c < d + 148) :
    a + 148 < d + 592 + b := by omega

theorem omega_149 (a b c d : Nat) (h1 : a + 149 < b) (h2 : b * 2 < c + 447) (h3 : c < d + 149) :
    a + 149 < d + 596 + b := by omega

theorem omega_150 (a b c d : Nat) (h1 : a + 150 < b) (h2 : b * 2 < c + 450) (h3 : c < d + 150) :
    a + 150 < d + 600 + b := by omega

theorem omega_151 (a b c d : Nat) (h1 : a + 151 < b) (h2 : b * 2 < c + 453) (h3 : c < d + 151) :
    a + 151 < d + 604 + b := by omega

theorem omega_152 (a b c d : Nat) (h1 : a + 152 < b) (h2 : b * 2 < c + 456) (h3 : c < d + 152) :
    a + 152 < d + 608 + b := by omega

theorem omega_153 (a b c d : Nat) (h1 : a + 153 < b) (h2 : b * 2 < c + 459) (h3 : c < d + 153) :
    a + 153 < d + 612 + b := by omega

theorem omega_154 (a b c d : Nat) (h1 : a + 154 < b) (h2 : b * 2 < c + 462) (h3 : c < d + 154) :
    a + 154 < d + 616 + b := by omega

theorem omega_155 (a b c d : Nat) (h1 : a + 155 < b) (h2 : b * 2 < c + 465) (h3 : c < d + 155) :
    a + 155 < d + 620 + b := by omega

theorem omega_156 (a b c d : Nat) (h1 : a + 156 < b) (h2 : b * 2 < c + 468) (h3 : c < d + 156) :
    a + 156 < d + 624 + b := by omega

theorem omega_157 (a b c d : Nat) (h1 : a + 157 < b) (h2 : b * 2 < c + 471) (h3 : c < d + 157) :
    a + 157 < d + 628 + b := by omega

theorem omega_158 (a b c d : Nat) (h1 : a + 158 < b) (h2 : b * 2 < c + 474) (h3 : c < d + 158) :
    a + 158 < d + 632 + b := by omega

theorem omega_159 (a b c d : Nat) (h1 : a + 159 < b) (h2 : b * 2 < c + 477) (h3 : c < d + 159) :
    a + 159 < d + 636 + b := by omega

theorem omega_160 (a b c d : Nat) (h1 : a + 160 < b) (h2 : b * 2 < c + 480) (h3 : c < d + 160) :
    a + 160 < d + 640 + b := by omega

theorem omega_161 (a b c d : Nat) (h1 : a + 161 < b) (h2 : b * 2 < c + 483) (h3 : c < d + 161) :
    a + 161 < d + 644 + b := by omega

theorem omega_162 (a b c d : Nat) (h1 : a + 162 < b) (h2 : b * 2 < c + 486) (h3 : c < d + 162) :
    a + 162 < d + 648 + b := by omega

theorem omega_163 (a b c d : Nat) (h1 : a + 163 < b) (h2 : b * 2 < c + 489) (h3 : c < d + 163) :
    a + 163 < d + 652 + b := by omega

theorem omega_164 (a b c d : Nat) (h1 : a + 164 < b) (h2 : b * 2 < c + 492) (h3 : c < d + 164) :
    a + 164 < d + 656 + b := by omega

theorem omega_165 (a b c d : Nat) (h1 : a + 165 < b) (h2 : b * 2 < c + 495) (h3 : c < d + 165) :
    a + 165 < d + 660 + b := by omega

theorem omega_166 (a b c d : Nat) (h1 : a + 166 < b) (h2 : b * 2 < c + 498) (h3 : c < d + 166) :
    a + 166 < d + 664 + b := by omega

theorem omega_167 (a b c d : Nat) (h1 : a + 167 < b) (h2 : b * 2 < c + 501) (h3 : c < d + 167) :
    a + 167 < d + 668 + b := by omega

theorem omega_168 (a b c d : Nat) (h1 : a + 168 < b) (h2 : b * 2 < c + 504) (h3 : c < d + 168) :
    a + 168 < d + 672 + b := by omega

theorem omega_169 (a b c d : Nat) (h1 : a + 169 < b) (h2 : b * 2 < c + 507) (h3 : c < d + 169) :
    a + 169 < d + 676 + b := by omega

theorem omega_170 (a b c d : Nat) (h1 : a + 170 < b) (h2 : b * 2 < c + 510) (h3 : c < d + 170) :
    a + 170 < d + 680 + b := by omega

theorem omega_171 (a b c d : Nat) (h1 : a + 171 < b) (h2 : b * 2 < c + 513) (h3 : c < d + 171) :
    a + 171 < d + 684 + b := by omega

theorem omega_172 (a b c d : Nat) (h1 : a + 172 < b) (h2 : b * 2 < c + 516) (h3 : c < d + 172) :
    a + 172 < d + 688 + b := by omega

theorem omega_173 (a b c d : Nat) (h1 : a + 173 < b) (h2 : b * 2 < c + 519) (h3 : c < d + 173) :
    a + 173 < d + 692 + b := by omega

theorem omega_174 (a b c d : Nat) (h1 : a + 174 < b) (h2 : b * 2 < c + 522) (h3 : c < d + 174) :
    a + 174 < d + 696 + b := by omega

theorem omega_175 (a b c d : Nat) (h1 : a + 175 < b) (h2 : b * 2 < c + 525) (h3 : c < d + 175) :
    a + 175 < d + 700 + b := by omega

theorem omega_176 (a b c d : Nat) (h1 : a + 176 < b) (h2 : b * 2 < c + 528) (h3 : c < d + 176) :
    a + 176 < d + 704 + b := by omega

theorem omega_177 (a b c d : Nat) (h1 : a + 177 < b) (h2 : b * 2 < c + 531) (h3 : c < d + 177) :
    a + 177 < d + 708 + b := by omega

theorem omega_178 (a b c d : Nat) (h1 : a + 178 < b) (h2 : b * 2 < c + 534) (h3 : c < d + 178) :
    a + 178 < d + 712 + b := by omega

theorem omega_179 (a b c d : Nat) (h1 : a + 179 < b) (h2 : b * 2 < c + 537) (h3 : c < d + 179) :
    a + 179 < d + 716 + b := by omega

theorem omega_180 (a b c d : Nat) (h1 : a + 180 < b) (h2 : b * 2 < c + 540) (h3 : c < d + 180) :
    a + 180 < d + 720 + b := by omega

theorem omega_181 (a b c d : Nat) (h1 : a + 181 < b) (h2 : b * 2 < c + 543) (h3 : c < d + 181) :
    a + 181 < d + 724 + b := by omega

theorem omega_182 (a b c d : Nat) (h1 : a + 182 < b) (h2 : b * 2 < c + 546) (h3 : c < d + 182) :
    a + 182 < d + 728 + b := by omega

theorem omega_183 (a b c d : Nat) (h1 : a + 183 < b) (h2 : b * 2 < c + 549) (h3 : c < d + 183) :
    a + 183 < d + 732 + b := by omega

theorem omega_184 (a b c d : Nat) (h1 : a + 184 < b) (h2 : b * 2 < c + 552) (h3 : c < d + 184) :
    a + 184 < d + 736 + b := by omega

theorem omega_185 (a b c d : Nat) (h1 : a + 185 < b) (h2 : b * 2 < c + 555) (h3 : c < d + 185) :
    a + 185 < d + 740 + b := by omega

theorem omega_186 (a b c d : Nat) (h1 : a + 186 < b) (h2 : b * 2 < c + 558) (h3 : c < d + 186) :
    a + 186 < d + 744 + b := by omega

theorem omega_187 (a b c d : Nat) (h1 : a + 187 < b) (h2 : b * 2 < c + 561) (h3 : c < d + 187) :
    a + 187 < d + 748 + b := by omega

theorem omega_188 (a b c d : Nat) (h1 : a + 188 < b) (h2 : b * 2 < c + 564) (h3 : c < d + 188) :
    a + 188 < d + 752 + b := by omega

theorem omega_189 (a b c d : Nat) (h1 : a + 189 < b) (h2 : b * 2 < c + 567) (h3 : c < d + 189) :
    a + 189 < d + 756 + b := by omega

theorem omega_190 (a b c d : Nat) (h1 : a + 190 < b) (h2 : b * 2 < c + 570) (h3 : c < d + 190) :
    a + 190 < d + 760 + b := by omega

theorem omega_191 (a b c d : Nat) (h1 : a + 191 < b) (h2 : b * 2 < c + 573) (h3 : c < d + 191) :
    a + 191 < d + 764 + b := by omega

theorem omega_192 (a b c d : Nat) (h1 : a + 192 < b) (h2 : b * 2 < c + 576) (h3 : c < d + 192) :
    a + 192 < d + 768 + b := by omega

theorem omega_193 (a b c d : Nat) (h1 : a + 193 < b) (h2 : b * 2 < c + 579) (h3 : c < d + 193) :
    a + 193 < d + 772 + b := by omega

theorem omega_194 (a b c d : Nat) (h1 : a + 194 < b) (h2 : b * 2 < c + 582) (h3 : c < d + 194) :
    a + 194 < d + 776 + b := by omega

theorem omega_195 (a b c d : Nat) (h1 : a + 195 < b) (h2 : b * 2 < c + 585) (h3 : c < d + 195) :
    a + 195 < d + 780 + b := by omega

theorem omega_196 (a b c d : Nat) (h1 : a + 196 < b) (h2 : b * 2 < c + 588) (h3 : c < d + 196) :
    a + 196 < d + 784 + b := by omega

theorem omega_197 (a b c d : Nat) (h1 : a + 197 < b) (h2 : b * 2 < c + 591) (h3 : c < d + 197) :
    a + 197 < d + 788 + b := by omega

theorem omega_198 (a b c d : Nat) (h1 : a + 198 < b) (h2 : b * 2 < c + 594) (h3 : c < d + 198) :
    a + 198 < d + 792 + b := by omega

theorem omega_199 (a b c d : Nat) (h1 : a + 199 < b) (h2 : b * 2 < c + 597) (h3 : c < d + 199) :
    a + 199 < d + 796 + b := by omega

theorem omega_200 (a b c d : Nat) (h1 : a + 200 < b) (h2 : b * 2 < c + 600) (h3 : c < d + 200) :
    a + 200 < d + 800 + b := by omega

theorem omega_201 (a b c d : Nat) (h1 : a + 201 < b) (h2 : b * 2 < c + 603) (h3 : c < d + 201) :
    a + 201 < d + 804 + b := by omega

theorem omega_202 (a b c d : Nat) (h1 : a + 202 < b) (h2 : b * 2 < c + 606) (h3 : c < d + 202) :
    a + 202 < d + 808 + b := by omega

theorem omega_203 (a b c d : Nat) (h1 : a + 203 < b) (h2 : b * 2 < c + 609) (h3 : c < d + 203) :
    a + 203 < d + 812 + b := by omega

theorem omega_204 (a b c d : Nat) (h1 : a + 204 < b) (h2 : b * 2 < c + 612) (h3 : c < d + 204) :
    a + 204 < d + 816 + b := by omega

theorem omega_205 (a b c d : Nat) (h1 : a + 205 < b) (h2 : b * 2 < c + 615) (h3 : c < d + 205) :
    a + 205 < d + 820 + b := by omega

theorem omega_206 (a b c d : Nat) (h1 : a + 206 < b) (h2 : b * 2 < c + 618) (h3 : c < d + 206) :
    a + 206 < d + 824 + b := by omega

theorem omega_207 (a b c d : Nat) (h1 : a + 207 < b) (h2 : b * 2 < c + 621) (h3 : c < d + 207) :
    a + 207 < d + 828 + b := by omega

theorem omega_208 (a b c d : Nat) (h1 : a + 208 < b) (h2 : b * 2 < c + 624) (h3 : c < d + 208) :
    a + 208 < d + 832 + b := by omega

theorem omega_209 (a b c d : Nat) (h1 : a + 209 < b) (h2 : b * 2 < c + 627) (h3 : c < d + 209) :
    a + 209 < d + 836 + b := by omega

theorem omega_210 (a b c d : Nat) (h1 : a + 210 < b) (h2 : b * 2 < c + 630) (h3 : c < d + 210) :
    a + 210 < d + 840 + b := by omega

theorem omega_211 (a b c d : Nat) (h1 : a + 211 < b) (h2 : b * 2 < c + 633) (h3 : c < d + 211) :
    a + 211 < d + 844 + b := by omega

theorem omega_212 (a b c d : Nat) (h1 : a + 212 < b) (h2 : b * 2 < c + 636) (h3 : c < d + 212) :
    a + 212 < d + 848 + b := by omega

theorem omega_213 (a b c d : Nat) (h1 : a + 213 < b) (h2 : b * 2 < c + 639) (h3 : c < d + 213) :
    a + 213 < d + 852 + b := by omega

theorem omega_214 (a b c d : Nat) (h1 : a + 214 < b) (h2 : b * 2 < c + 642) (h3 : c < d + 214) :
    a + 214 < d + 856 + b := by omega

theorem omega_215 (a b c d : Nat) (h1 : a + 215 < b) (h2 : b * 2 < c + 645) (h3 : c < d + 215) :
    a + 215 < d + 860 + b := by omega

theorem omega_216 (a b c d : Nat) (h1 : a + 216 < b) (h2 : b * 2 < c + 648) (h3 : c < d + 216) :
    a + 216 < d + 864 + b := by omega

theorem omega_217 (a b c d : Nat) (h1 : a + 217 < b) (h2 : b * 2 < c + 651) (h3 : c < d + 217) :
    a + 217 < d + 868 + b := by omega

theorem omega_218 (a b c d : Nat) (h1 : a + 218 < b) (h2 : b * 2 < c + 654) (h3 : c < d + 218) :
    a + 218 < d + 872 + b := by omega

theorem omega_219 (a b c d : Nat) (h1 : a + 219 < b) (h2 : b * 2 < c + 657) (h3 : c < d + 219) :
    a + 219 < d + 876 + b := by omega

theorem omega_220 (a b c d : Nat) (h1 : a + 220 < b) (h2 : b * 2 < c + 660) (h3 : c < d + 220) :
    a + 220 < d + 880 + b := by omega

theorem omega_221 (a b c d : Nat) (h1 : a + 221 < b) (h2 : b * 2 < c + 663) (h3 : c < d + 221) :
    a + 221 < d + 884 + b := by omega

theorem omega_222 (a b c d : Nat) (h1 : a + 222 < b) (h2 : b * 2 < c + 666) (h3 : c < d + 222) :
    a + 222 < d + 888 + b := by omega

theorem omega_223 (a b c d : Nat) (h1 : a + 223 < b) (h2 : b * 2 < c + 669) (h3 : c < d + 223) :
    a + 223 < d + 892 + b := by omega

theorem omega_224 (a b c d : Nat) (h1 : a + 224 < b) (h2 : b * 2 < c + 672) (h3 : c < d + 224) :
    a + 224 < d + 896 + b := by omega

theorem omega_225 (a b c d : Nat) (h1 : a + 225 < b) (h2 : b * 2 < c + 675) (h3 : c < d + 225) :
    a + 225 < d + 900 + b := by omega

theorem omega_226 (a b c d : Nat) (h1 : a + 226 < b) (h2 : b * 2 < c + 678) (h3 : c < d + 226) :
    a + 226 < d + 904 + b := by omega

theorem omega_227 (a b c d : Nat) (h1 : a + 227 < b) (h2 : b * 2 < c + 681) (h3 : c < d + 227) :
    a + 227 < d + 908 + b := by omega

theorem omega_228 (a b c d : Nat) (h1 : a + 228 < b) (h2 : b * 2 < c + 684) (h3 : c < d + 228) :
    a + 228 < d + 912 + b := by omega

theorem omega_229 (a b c d : Nat) (h1 : a + 229 < b) (h2 : b * 2 < c + 687) (h3 : c < d + 229) :
    a + 229 < d + 916 + b := by omega

theorem omega_230 (a b c d : Nat) (h1 : a + 230 < b) (h2 : b * 2 < c + 690) (h3 : c < d + 230) :
    a + 230 < d + 920 + b := by omega

theorem omega_231 (a b c d : Nat) (h1 : a + 231 < b) (h2 : b * 2 < c + 693) (h3 : c < d + 231) :
    a + 231 < d + 924 + b := by omega

theorem omega_232 (a b c d : Nat) (h1 : a + 232 < b) (h2 : b * 2 < c + 696) (h3 : c < d + 232) :
    a + 232 < d + 928 + b := by omega

theorem omega_233 (a b c d : Nat) (h1 : a + 233 < b) (h2 : b * 2 < c + 699) (h3 : c < d + 233) :
    a + 233 < d + 932 + b := by omega

theorem omega_234 (a b c d : Nat) (h1 : a + 234 < b) (h2 : b * 2 < c + 702) (h3 : c < d + 234) :
    a + 234 < d + 936 + b := by omega

theorem omega_235 (a b c d : Nat) (h1 : a + 235 < b) (h2 : b * 2 < c + 705) (h3 : c < d + 235) :
    a + 235 < d + 940 + b := by omega

theorem omega_236 (a b c d : Nat) (h1 : a + 236 < b) (h2 : b * 2 < c + 708) (h3 : c < d + 236) :
    a + 236 < d + 944 + b := by omega

theorem omega_237 (a b c d : Nat) (h1 : a + 237 < b) (h2 : b * 2 < c + 711) (h3 : c < d + 237) :
    a + 237 < d + 948 + b := by omega

theorem omega_238 (a b c d : Nat) (h1 : a + 238 < b) (h2 : b * 2 < c + 714) (h3 : c < d + 238) :
    a + 238 < d + 952 + b := by omega

theorem omega_239 (a b c d : Nat) (h1 : a + 239 < b) (h2 : b * 2 < c + 717) (h3 : c < d + 239) :
    a + 239 < d + 956 + b := by omega

theorem omega_240 (a b c d : Nat) (h1 : a + 240 < b) (h2 : b * 2 < c + 720) (h3 : c < d + 240) :
    a + 240 < d + 960 + b := by omega

theorem omega_241 (a b c d : Nat) (h1 : a + 241 < b) (h2 : b * 2 < c + 723) (h3 : c < d + 241) :
    a + 241 < d + 964 + b := by omega

theorem omega_242 (a b c d : Nat) (h1 : a + 242 < b) (h2 : b * 2 < c + 726) (h3 : c < d + 242) :
    a + 242 < d + 968 + b := by omega

theorem omega_243 (a b c d : Nat) (h1 : a + 243 < b) (h2 : b * 2 < c + 729) (h3 : c < d + 243) :
    a + 243 < d + 972 + b := by omega

theorem omega_244 (a b c d : Nat) (h1 : a + 244 < b) (h2 : b * 2 < c + 732) (h3 : c < d + 244) :
    a + 244 < d + 976 + b := by omega

theorem omega_245 (a b c d : Nat) (h1 : a + 245 < b) (h2 : b * 2 < c + 735) (h3 : c < d + 245) :
    a + 245 < d + 980 + b := by omega

theorem omega_246 (a b c d : Nat) (h1 : a + 246 < b) (h2 : b * 2 < c + 738) (h3 : c < d + 246) :
    a + 246 < d + 984 + b := by omega

theorem omega_247 (a b c d : Nat) (h1 : a + 247 < b) (h2 : b * 2 < c + 741) (h3 : c < d + 247) :
    a + 247 < d + 988 + b := by omega

theorem omega_248 (a b c d : Nat) (h1 : a + 248 < b) (h2 : b * 2 < c + 744) (h3 : c < d + 248) :
    a + 248 < d + 992 + b := by omega

theorem omega_249 (a b c d : Nat) (h1 : a + 249 < b) (h2 : b * 2 < c + 747) (h3 : c < d + 249) :
    a + 249 < d + 996 + b := by omega

theorem omega_250 (a b c d : Nat) (h1 : a + 250 < b) (h2 : b * 2 < c + 750) (h3 : c < d + 250) :
    a + 250 < d + 1000 + b := by omega

theorem omega_251 (a b c d : Nat) (h1 : a + 251 < b) (h2 : b * 2 < c + 753) (h3 : c < d + 251) :
    a + 251 < d + 1004 + b := by omega

theorem omega_252 (a b c d : Nat) (h1 : a + 252 < b) (h2 : b * 2 < c + 756) (h3 : c < d + 252) :
    a + 252 < d + 1008 + b := by omega

theorem omega_253 (a b c d : Nat) (h1 : a + 253 < b) (h2 : b * 2 < c + 759) (h3 : c < d + 253) :
    a + 253 < d + 1012 + b := by omega

theorem omega_254 (a b c d : Nat) (h1 : a + 254 < b) (h2 : b * 2 < c + 762) (h3 : c < d + 254) :
    a + 254 < d + 1016 + b := by omega

theorem omega_255 (a b c d : Nat) (h1 : a + 255 < b) (h2 : b * 2 < c + 765) (h3 : c < d + 255) :
    a + 255 < d + 1020 + b := by omega

theorem omega_256 (a b c d : Nat) (h1 : a + 256 < b) (h2 : b * 2 < c + 768) (h3 : c < d + 256) :
    a + 256 < d + 1024 + b := by omega

theorem omega_257 (a b c d : Nat) (h1 : a + 257 < b) (h2 : b * 2 < c + 771) (h3 : c < d + 257) :
    a + 257 < d + 1028 + b := by omega

theorem omega_258 (a b c d : Nat) (h1 : a + 258 < b) (h2 : b * 2 < c + 774) (h3 : c < d + 258) :
    a + 258 < d + 1032 + b := by omega

theorem omega_259 (a b c d : Nat) (h1 : a + 259 < b) (h2 : b * 2 < c + 777) (h3 : c < d + 259) :
    a + 259 < d + 1036 + b := by omega

theorem omega_260 (a b c d : Nat) (h1 : a + 260 < b) (h2 : b * 2 < c + 780) (h3 : c < d + 260) :
    a + 260 < d + 1040 + b := by omega

theorem omega_261 (a b c d : Nat) (h1 : a + 261 < b) (h2 : b * 2 < c + 783) (h3 : c < d + 261) :
    a + 261 < d + 1044 + b := by omega

theorem omega_262 (a b c d : Nat) (h1 : a + 262 < b) (h2 : b * 2 < c + 786) (h3 : c < d + 262) :
    a + 262 < d + 1048 + b := by omega

theorem omega_263 (a b c d : Nat) (h1 : a + 263 < b) (h2 : b * 2 < c + 789) (h3 : c < d + 263) :
    a + 263 < d + 1052 + b := by omega

theorem omega_264 (a b c d : Nat) (h1 : a + 264 < b) (h2 : b * 2 < c + 792) (h3 : c < d + 264) :
    a + 264 < d + 1056 + b := by omega

theorem omega_265 (a b c d : Nat) (h1 : a + 265 < b) (h2 : b * 2 < c + 795) (h3 : c < d + 265) :
    a + 265 < d + 1060 + b := by omega

theorem omega_266 (a b c d : Nat) (h1 : a + 266 < b) (h2 : b * 2 < c + 798) (h3 : c < d + 266) :
    a + 266 < d + 1064 + b := by omega

theorem omega_267 (a b c d : Nat) (h1 : a + 267 < b) (h2 : b * 2 < c + 801) (h3 : c < d + 267) :
    a + 267 < d + 1068 + b := by omega

theorem omega_268 (a b c d : Nat) (h1 : a + 268 < b) (h2 : b * 2 < c + 804) (h3 : c < d + 268) :
    a + 268 < d + 1072 + b := by omega

theorem omega_269 (a b c d : Nat) (h1 : a + 269 < b) (h2 : b * 2 < c + 807) (h3 : c < d + 269) :
    a + 269 < d + 1076 + b := by omega

theorem omega_270 (a b c d : Nat) (h1 : a + 270 < b) (h2 : b * 2 < c + 810) (h3 : c < d + 270) :
    a + 270 < d + 1080 + b := by omega

theorem omega_271 (a b c d : Nat) (h1 : a + 271 < b) (h2 : b * 2 < c + 813) (h3 : c < d + 271) :
    a + 271 < d + 1084 + b := by omega

theorem omega_272 (a b c d : Nat) (h1 : a + 272 < b) (h2 : b * 2 < c + 816) (h3 : c < d + 272) :
    a + 272 < d + 1088 + b := by omega

theorem omega_273 (a b c d : Nat) (h1 : a + 273 < b) (h2 : b * 2 < c + 819) (h3 : c < d + 273) :
    a + 273 < d + 1092 + b := by omega

theorem omega_274 (a b c d : Nat) (h1 : a + 274 < b) (h2 : b * 2 < c + 822) (h3 : c < d + 274) :
    a + 274 < d + 1096 + b := by omega

theorem omega_275 (a b c d : Nat) (h1 : a + 275 < b) (h2 : b * 2 < c + 825) (h3 : c < d + 275) :
    a + 275 < d + 1100 + b := by omega

theorem omega_276 (a b c d : Nat) (h1 : a + 276 < b) (h2 : b * 2 < c + 828) (h3 : c < d + 276) :
    a + 276 < d + 1104 + b := by omega

theorem omega_277 (a b c d : Nat) (h1 : a + 277 < b) (h2 : b * 2 < c + 831) (h3 : c < d + 277) :
    a + 277 < d + 1108 + b := by omega

theorem omega_278 (a b c d : Nat) (h1 : a + 278 < b) (h2 : b * 2 < c + 834) (h3 : c < d + 278) :
    a + 278 < d + 1112 + b := by omega

theorem omega_279 (a b c d : Nat) (h1 : a + 279 < b) (h2 : b * 2 < c + 837) (h3 : c < d + 279) :
    a + 279 < d + 1116 + b := by omega

theorem omega_280 (a b c d : Nat) (h1 : a + 280 < b) (h2 : b * 2 < c + 840) (h3 : c < d + 280) :
    a + 280 < d + 1120 + b := by omega

theorem omega_281 (a b c d : Nat) (h1 : a + 281 < b) (h2 : b * 2 < c + 843) (h3 : c < d + 281) :
    a + 281 < d + 1124 + b := by omega

theorem omega_282 (a b c d : Nat) (h1 : a + 282 < b) (h2 : b * 2 < c + 846) (h3 : c < d + 282) :
    a + 282 < d + 1128 + b := by omega

theorem omega_283 (a b c d : Nat) (h1 : a + 283 < b) (h2 : b * 2 < c + 849) (h3 : c < d + 283) :
    a + 283 < d + 1132 + b := by omega

theorem omega_284 (a b c d : Nat) (h1 : a + 284 < b) (h2 : b * 2 < c + 852) (h3 : c < d + 284) :
    a + 284 < d + 1136 + b := by omega

theorem omega_285 (a b c d : Nat) (h1 : a + 285 < b) (h2 : b * 2 < c + 855) (h3 : c < d + 285) :
    a + 285 < d + 1140 + b := by omega

theorem omega_286 (a b c d : Nat) (h1 : a + 286 < b) (h2 : b * 2 < c + 858) (h3 : c < d + 286) :
    a + 286 < d + 1144 + b := by omega

theorem omega_287 (a b c d : Nat) (h1 : a + 287 < b) (h2 : b * 2 < c + 861) (h3 : c < d + 287) :
    a + 287 < d + 1148 + b := by omega

theorem omega_288 (a b c d : Nat) (h1 : a + 288 < b) (h2 : b * 2 < c + 864) (h3 : c < d + 288) :
    a + 288 < d + 1152 + b := by omega

theorem omega_289 (a b c d : Nat) (h1 : a + 289 < b) (h2 : b * 2 < c + 867) (h3 : c < d + 289) :
    a + 289 < d + 1156 + b := by omega

theorem omega_290 (a b c d : Nat) (h1 : a + 290 < b) (h2 : b * 2 < c + 870) (h3 : c < d + 290) :
    a + 290 < d + 1160 + b := by omega

theorem omega_291 (a b c d : Nat) (h1 : a + 291 < b) (h2 : b * 2 < c + 873) (h3 : c < d + 291) :
    a + 291 < d + 1164 + b := by omega

theorem omega_292 (a b c d : Nat) (h1 : a + 292 < b) (h2 : b * 2 < c + 876) (h3 : c < d + 292) :
    a + 292 < d + 1168 + b := by omega

theorem omega_293 (a b c d : Nat) (h1 : a + 293 < b) (h2 : b * 2 < c + 879) (h3 : c < d + 293) :
    a + 293 < d + 1172 + b := by omega

theorem omega_294 (a b c d : Nat) (h1 : a + 294 < b) (h2 : b * 2 < c + 882) (h3 : c < d + 294) :
    a + 294 < d + 1176 + b := by omega

theorem omega_295 (a b c d : Nat) (h1 : a + 295 < b) (h2 : b * 2 < c + 885) (h3 : c < d + 295) :
    a + 295 < d + 1180 + b := by omega

theorem omega_296 (a b c d : Nat) (h1 : a + 296 < b) (h2 : b * 2 < c + 888) (h3 : c < d + 296) :
    a + 296 < d + 1184 + b := by omega

theorem omega_297 (a b c d : Nat) (h1 : a + 297 < b) (h2 : b * 2 < c + 891) (h3 : c < d + 297) :
    a + 297 < d + 1188 + b := by omega

theorem omega_298 (a b c d : Nat) (h1 : a + 298 < b) (h2 : b * 2 < c + 894) (h3 : c < d + 298) :
    a + 298 < d + 1192 + b := by omega

theorem omega_299 (a b c d : Nat) (h1 : a + 299 < b) (h2 : b * 2 < c + 897) (h3 : c < d + 299) :
    a + 299 < d + 1196 + b := by omega

theorem omega_300 (a b c d : Nat) (h1 : a + 300 < b) (h2 : b * 2 < c + 900) (h3 : c < d + 300) :
    a + 300 < d + 1200 + b := by omega

theorem omega_301 (a b c d : Nat) (h1 : a + 301 < b) (h2 : b * 2 < c + 903) (h3 : c < d + 301) :
    a + 301 < d + 1204 + b := by omega

theorem omega_302 (a b c d : Nat) (h1 : a + 302 < b) (h2 : b * 2 < c + 906) (h3 : c < d + 302) :
    a + 302 < d + 1208 + b := by omega

theorem omega_303 (a b c d : Nat) (h1 : a + 303 < b) (h2 : b * 2 < c + 909) (h3 : c < d + 303) :
    a + 303 < d + 1212 + b := by omega

theorem omega_304 (a b c d : Nat) (h1 : a + 304 < b) (h2 : b * 2 < c + 912) (h3 : c < d + 304) :
    a + 304 < d + 1216 + b := by omega

theorem omega_305 (a b c d : Nat) (h1 : a + 305 < b) (h2 : b * 2 < c + 915) (h3 : c < d + 305) :
    a + 305 < d + 1220 + b := by omega

theorem omega_306 (a b c d : Nat) (h1 : a + 306 < b) (h2 : b * 2 < c + 918) (h3 : c < d + 306) :
    a + 306 < d + 1224 + b := by omega

theorem omega_307 (a b c d : Nat) (h1 : a + 307 < b) (h2 : b * 2 < c + 921) (h3 : c < d + 307) :
    a + 307 < d + 1228 + b := by omega

theorem omega_308 (a b c d : Nat) (h1 : a + 308 < b) (h2 : b * 2 < c + 924) (h3 : c < d + 308) :
    a + 308 < d + 1232 + b := by omega

theorem omega_309 (a b c d : Nat) (h1 : a + 309 < b) (h2 : b * 2 < c + 927) (h3 : c < d + 309) :
    a + 309 < d + 1236 + b := by omega

theorem omega_310 (a b c d : Nat) (h1 : a + 310 < b) (h2 : b * 2 < c + 930) (h3 : c < d + 310) :
    a + 310 < d + 1240 + b := by omega

theorem omega_311 (a b c d : Nat) (h1 : a + 311 < b) (h2 : b * 2 < c + 933) (h3 : c < d + 311) :
    a + 311 < d + 1244 + b := by omega

theorem omega_312 (a b c d : Nat) (h1 : a + 312 < b) (h2 : b * 2 < c + 936) (h3 : c < d + 312) :
    a + 312 < d + 1248 + b := by omega

theorem omega_313 (a b c d : Nat) (h1 : a + 313 < b) (h2 : b * 2 < c + 939) (h3 : c < d + 313) :
    a + 313 < d + 1252 + b := by omega

theorem omega_314 (a b c d : Nat) (h1 : a + 314 < b) (h2 : b * 2 < c + 942) (h3 : c < d + 314) :
    a + 314 < d + 1256 + b := by omega

theorem omega_315 (a b c d : Nat) (h1 : a + 315 < b) (h2 : b * 2 < c + 945) (h3 : c < d + 315) :
    a + 315 < d + 1260 + b := by omega

theorem omega_316 (a b c d : Nat) (h1 : a + 316 < b) (h2 : b * 2 < c + 948) (h3 : c < d + 316) :
    a + 316 < d + 1264 + b := by omega

theorem omega_317 (a b c d : Nat) (h1 : a + 317 < b) (h2 : b * 2 < c + 951) (h3 : c < d + 317) :
    a + 317 < d + 1268 + b := by omega

theorem omega_318 (a b c d : Nat) (h1 : a + 318 < b) (h2 : b * 2 < c + 954) (h3 : c < d + 318) :
    a + 318 < d + 1272 + b := by omega

theorem omega_319 (a b c d : Nat) (h1 : a + 319 < b) (h2 : b * 2 < c + 957) (h3 : c < d + 319) :
    a + 319 < d + 1276 + b := by omega

theorem omega_320 (a b c d : Nat) (h1 : a + 320 < b) (h2 : b * 2 < c + 960) (h3 : c < d + 320) :
    a + 320 < d + 1280 + b := by omega

theorem omega_321 (a b c d : Nat) (h1 : a + 321 < b) (h2 : b * 2 < c + 963) (h3 : c < d + 321) :
    a + 321 < d + 1284 + b := by omega

theorem omega_322 (a b c d : Nat) (h1 : a + 322 < b) (h2 : b * 2 < c + 966) (h3 : c < d + 322) :
    a + 322 < d + 1288 + b := by omega

theorem omega_323 (a b c d : Nat) (h1 : a + 323 < b) (h2 : b * 2 < c + 969) (h3 : c < d + 323) :
    a + 323 < d + 1292 + b := by omega

theorem omega_324 (a b c d : Nat) (h1 : a + 324 < b) (h2 : b * 2 < c + 972) (h3 : c < d + 324) :
    a + 324 < d + 1296 + b := by omega

theorem omega_325 (a b c d : Nat) (h1 : a + 325 < b) (h2 : b * 2 < c + 975) (h3 : c < d + 325) :
    a + 325 < d + 1300 + b := by omega

theorem omega_326 (a b c d : Nat) (h1 : a + 326 < b) (h2 : b * 2 < c + 978) (h3 : c < d + 326) :
    a + 326 < d + 1304 + b := by omega

theorem omega_327 (a b c d : Nat) (h1 : a + 327 < b) (h2 : b * 2 < c + 981) (h3 : c < d + 327) :
    a + 327 < d + 1308 + b := by omega

theorem omega_328 (a b c d : Nat) (h1 : a + 328 < b) (h2 : b * 2 < c + 984) (h3 : c < d + 328) :
    a + 328 < d + 1312 + b := by omega

theorem omega_329 (a b c d : Nat) (h1 : a + 329 < b) (h2 : b * 2 < c + 987) (h3 : c < d + 329) :
    a + 329 < d + 1316 + b := by omega

theorem omega_330 (a b c d : Nat) (h1 : a + 330 < b) (h2 : b * 2 < c + 990) (h3 : c < d + 330) :
    a + 330 < d + 1320 + b := by omega

theorem omega_331 (a b c d : Nat) (h1 : a + 331 < b) (h2 : b * 2 < c + 993) (h3 : c < d + 331) :
    a + 331 < d + 1324 + b := by omega

theorem omega_332 (a b c d : Nat) (h1 : a + 332 < b) (h2 : b * 2 < c + 996) (h3 : c < d + 332) :
    a + 332 < d + 1328 + b := by omega

theorem omega_333 (a b c d : Nat) (h1 : a + 333 < b) (h2 : b * 2 < c + 999) (h3 : c < d + 333) :
    a + 333 < d + 1332 + b := by omega

theorem omega_334 (a b c d : Nat) (h1 : a + 334 < b) (h2 : b * 2 < c + 1002) (h3 : c < d + 334) :
    a + 334 < d + 1336 + b := by omega

theorem omega_335 (a b c d : Nat) (h1 : a + 335 < b) (h2 : b * 2 < c + 1005) (h3 : c < d + 335) :
    a + 335 < d + 1340 + b := by omega

theorem omega_336 (a b c d : Nat) (h1 : a + 336 < b) (h2 : b * 2 < c + 1008) (h3 : c < d + 336) :
    a + 336 < d + 1344 + b := by omega

theorem omega_337 (a b c d : Nat) (h1 : a + 337 < b) (h2 : b * 2 < c + 1011) (h3 : c < d + 337) :
    a + 337 < d + 1348 + b := by omega

theorem omega_338 (a b c d : Nat) (h1 : a + 338 < b) (h2 : b * 2 < c + 1014) (h3 : c < d + 338) :
    a + 338 < d + 1352 + b := by omega

theorem omega_339 (a b c d : Nat) (h1 : a + 339 < b) (h2 : b * 2 < c + 1017) (h3 : c < d + 339) :
    a + 339 < d + 1356 + b := by omega

theorem omega_340 (a b c d : Nat) (h1 : a + 340 < b) (h2 : b * 2 < c + 1020) (h3 : c < d + 340) :
    a + 340 < d + 1360 + b := by omega

theorem omega_341 (a b c d : Nat) (h1 : a + 341 < b) (h2 : b * 2 < c + 1023) (h3 : c < d + 341) :
    a + 341 < d + 1364 + b := by omega

theorem omega_342 (a b c d : Nat) (h1 : a + 342 < b) (h2 : b * 2 < c + 1026) (h3 : c < d + 342) :
    a + 342 < d + 1368 + b := by omega

theorem omega_343 (a b c d : Nat) (h1 : a + 343 < b) (h2 : b * 2 < c + 1029) (h3 : c < d + 343) :
    a + 343 < d + 1372 + b := by omega

theorem omega_344 (a b c d : Nat) (h1 : a + 344 < b) (h2 : b * 2 < c + 1032) (h3 : c < d + 344) :
    a + 344 < d + 1376 + b := by omega

theorem omega_345 (a b c d : Nat) (h1 : a + 345 < b) (h2 : b * 2 < c + 1035) (h3 : c < d + 345) :
    a + 345 < d + 1380 + b := by omega

theorem omega_346 (a b c d : Nat) (h1 : a + 346 < b) (h2 : b * 2 < c + 1038) (h3 : c < d + 346) :
    a + 346 < d + 1384 + b := by omega

theorem omega_347 (a b c d : Nat) (h1 : a + 347 < b) (h2 : b * 2 < c + 1041) (h3 : c < d + 347) :
    a + 347 < d + 1388 + b := by omega

theorem omega_348 (a b c d : Nat) (h1 : a + 348 < b) (h2 : b * 2 < c + 1044) (h3 : c < d + 348) :
    a + 348 < d + 1392 + b := by omega

theorem omega_349 (a b c d : Nat) (h1 : a + 349 < b) (h2 : b * 2 < c + 1047) (h3 : c < d + 349) :
    a + 349 < d + 1396 + b := by omega

theorem omega_350 (a b c d : Nat) (h1 : a + 350 < b) (h2 : b * 2 < c + 1050) (h3 : c < d + 350) :
    a + 350 < d + 1400 + b := by omega

theorem omega_351 (a b c d : Nat) (h1 : a + 351 < b) (h2 : b * 2 < c + 1053) (h3 : c < d + 351) :
    a + 351 < d + 1404 + b := by omega

theorem omega_352 (a b c d : Nat) (h1 : a + 352 < b) (h2 : b * 2 < c + 1056) (h3 : c < d + 352) :
    a + 352 < d + 1408 + b := by omega

theorem omega_353 (a b c d : Nat) (h1 : a + 353 < b) (h2 : b * 2 < c + 1059) (h3 : c < d + 353) :
    a + 353 < d + 1412 + b := by omega

theorem omega_354 (a b c d : Nat) (h1 : a + 354 < b) (h2 : b * 2 < c + 1062) (h3 : c < d + 354) :
    a + 354 < d + 1416 + b := by omega

theorem omega_355 (a b c d : Nat) (h1 : a + 355 < b) (h2 : b * 2 < c + 1065) (h3 : c < d + 355) :
    a + 355 < d + 1420 + b := by omega

theorem omega_356 (a b c d : Nat) (h1 : a + 356 < b) (h2 : b * 2 < c + 1068) (h3 : c < d + 356) :
    a + 356 < d + 1424 + b := by omega

theorem omega_357 (a b c d : Nat) (h1 : a + 357 < b) (h2 : b * 2 < c + 1071) (h3 : c < d + 357) :
    a + 357 < d + 1428 + b := by omega

theorem omega_358 (a b c d : Nat) (h1 : a + 358 < b) (h2 : b * 2 < c + 1074) (h3 : c < d + 358) :
    a + 358 < d + 1432 + b := by omega

theorem omega_359 (a b c d : Nat) (h1 : a + 359 < b) (h2 : b * 2 < c + 1077) (h3 : c < d + 359) :
    a + 359 < d + 1436 + b := by omega

theorem omega_360 (a b c d : Nat) (h1 : a + 360 < b) (h2 : b * 2 < c + 1080) (h3 : c < d + 360) :
    a + 360 < d + 1440 + b := by omega

theorem omega_361 (a b c d : Nat) (h1 : a + 361 < b) (h2 : b * 2 < c + 1083) (h3 : c < d + 361) :
    a + 361 < d + 1444 + b := by omega

theorem omega_362 (a b c d : Nat) (h1 : a + 362 < b) (h2 : b * 2 < c + 1086) (h3 : c < d + 362) :
    a + 362 < d + 1448 + b := by omega

theorem omega_363 (a b c d : Nat) (h1 : a + 363 < b) (h2 : b * 2 < c + 1089) (h3 : c < d + 363) :
    a + 363 < d + 1452 + b := by omega

theorem omega_364 (a b c d : Nat) (h1 : a + 364 < b) (h2 : b * 2 < c + 1092) (h3 : c < d + 364) :
    a + 364 < d + 1456 + b := by omega

theorem omega_365 (a b c d : Nat) (h1 : a + 365 < b) (h2 : b * 2 < c + 1095) (h3 : c < d + 365) :
    a + 365 < d + 1460 + b := by omega

theorem omega_366 (a b c d : Nat) (h1 : a + 366 < b) (h2 : b * 2 < c + 1098) (h3 : c < d + 366) :
    a + 366 < d + 1464 + b := by omega

theorem omega_367 (a b c d : Nat) (h1 : a + 367 < b) (h2 : b * 2 < c + 1101) (h3 : c < d + 367) :
    a + 367 < d + 1468 + b := by omega

theorem omega_368 (a b c d : Nat) (h1 : a + 368 < b) (h2 : b * 2 < c + 1104) (h3 : c < d + 368) :
    a + 368 < d + 1472 + b := by omega

theorem omega_369 (a b c d : Nat) (h1 : a + 369 < b) (h2 : b * 2 < c + 1107) (h3 : c < d + 369) :
    a + 369 < d + 1476 + b := by omega

theorem omega_370 (a b c d : Nat) (h1 : a + 370 < b) (h2 : b * 2 < c + 1110) (h3 : c < d + 370) :
    a + 370 < d + 1480 + b := by omega

theorem omega_371 (a b c d : Nat) (h1 : a + 371 < b) (h2 : b * 2 < c + 1113) (h3 : c < d + 371) :
    a + 371 < d + 1484 + b := by omega

theorem omega_372 (a b c d : Nat) (h1 : a + 372 < b) (h2 : b * 2 < c + 1116) (h3 : c < d + 372) :
    a + 372 < d + 1488 + b := by omega

theorem omega_373 (a b c d : Nat) (h1 : a + 373 < b) (h2 : b * 2 < c + 1119) (h3 : c < d + 373) :
    a + 373 < d + 1492 + b := by omega

theorem omega_374 (a b c d : Nat) (h1 : a + 374 < b) (h2 : b * 2 < c + 1122) (h3 : c < d + 374) :
    a + 374 < d + 1496 + b := by omega

theorem omega_375 (a b c d : Nat) (h1 : a + 375 < b) (h2 : b * 2 < c + 1125) (h3 : c < d + 375) :
    a + 375 < d + 1500 + b := by omega

theorem omega_376 (a b c d : Nat) (h1 : a + 376 < b) (h2 : b * 2 < c + 1128) (h3 : c < d + 376) :
    a + 376 < d + 1504 + b := by omega

theorem omega_377 (a b c d : Nat) (h1 : a + 377 < b) (h2 : b * 2 < c + 1131) (h3 : c < d + 377) :
    a + 377 < d + 1508 + b := by omega

theorem omega_378 (a b c d : Nat) (h1 : a + 378 < b) (h2 : b * 2 < c + 1134) (h3 : c < d + 378) :
    a + 378 < d + 1512 + b := by omega

theorem omega_379 (a b c d : Nat) (h1 : a + 379 < b) (h2 : b * 2 < c + 1137) (h3 : c < d + 379) :
    a + 379 < d + 1516 + b := by omega

theorem omega_380 (a b c d : Nat) (h1 : a + 380 < b) (h2 : b * 2 < c + 1140) (h3 : c < d + 380) :
    a + 380 < d + 1520 + b := by omega

theorem omega_381 (a b c d : Nat) (h1 : a + 381 < b) (h2 : b * 2 < c + 1143) (h3 : c < d + 381) :
    a + 381 < d + 1524 + b := by omega

theorem omega_382 (a b c d : Nat) (h1 : a + 382 < b) (h2 : b * 2 < c + 1146) (h3 : c < d + 382) :
    a + 382 < d + 1528 + b := by omega

theorem omega_383 (a b c d : Nat) (h1 : a + 383 < b) (h2 : b * 2 < c + 1149) (h3 : c < d + 383) :
    a + 383 < d + 1532 + b := by omega

theorem omega_384 (a b c d : Nat) (h1 : a + 384 < b) (h2 : b * 2 < c + 1152) (h3 : c < d + 384) :
    a + 384 < d + 1536 + b := by omega

theorem omega_385 (a b c d : Nat) (h1 : a + 385 < b) (h2 : b * 2 < c + 1155) (h3 : c < d + 385) :
    a + 385 < d + 1540 + b := by omega

theorem omega_386 (a b c d : Nat) (h1 : a + 386 < b) (h2 : b * 2 < c + 1158) (h3 : c < d + 386) :
    a + 386 < d + 1544 + b := by omega

theorem omega_387 (a b c d : Nat) (h1 : a + 387 < b) (h2 : b * 2 < c + 1161) (h3 : c < d + 387) :
    a + 387 < d + 1548 + b := by omega

theorem omega_388 (a b c d : Nat) (h1 : a + 388 < b) (h2 : b * 2 < c + 1164) (h3 : c < d + 388) :
    a + 388 < d + 1552 + b := by omega

theorem omega_389 (a b c d : Nat) (h1 : a + 389 < b) (h2 : b * 2 < c + 1167) (h3 : c < d + 389) :
    a + 389 < d + 1556 + b := by omega

theorem omega_390 (a b c d : Nat) (h1 : a + 390 < b) (h2 : b * 2 < c + 1170) (h3 : c < d + 390) :
    a + 390 < d + 1560 + b := by omega

theorem omega_391 (a b c d : Nat) (h1 : a + 391 < b) (h2 : b * 2 < c + 1173) (h3 : c < d + 391) :
    a + 391 < d + 1564 + b := by omega

theorem omega_392 (a b c d : Nat) (h1 : a + 392 < b) (h2 : b * 2 < c + 1176) (h3 : c < d + 392) :
    a + 392 < d + 1568 + b := by omega

theorem omega_393 (a b c d : Nat) (h1 : a + 393 < b) (h2 : b * 2 < c + 1179) (h3 : c < d + 393) :
    a + 393 < d + 1572 + b := by omega

theorem omega_394 (a b c d : Nat) (h1 : a + 394 < b) (h2 : b * 2 < c + 1182) (h3 : c < d + 394) :
    a + 394 < d + 1576 + b := by omega

theorem omega_395 (a b c d : Nat) (h1 : a + 395 < b) (h2 : b * 2 < c + 1185) (h3 : c < d + 395) :
    a + 395 < d + 1580 + b := by omega

theorem omega_396 (a b c d : Nat) (h1 : a + 396 < b) (h2 : b * 2 < c + 1188) (h3 : c < d + 396) :
    a + 396 < d + 1584 + b := by omega

theorem omega_397 (a b c d : Nat) (h1 : a + 397 < b) (h2 : b * 2 < c + 1191) (h3 : c < d + 397) :
    a + 397 < d + 1588 + b := by omega

theorem omega_398 (a b c d : Nat) (h1 : a + 398 < b) (h2 : b * 2 < c + 1194) (h3 : c < d + 398) :
    a + 398 < d + 1592 + b := by omega

theorem omega_399 (a b c d : Nat) (h1 : a + 399 < b) (h2 : b * 2 < c + 1197) (h3 : c < d + 399) :
    a + 399 < d + 1596 + b := by omega

theorem omega_400 (a b c d : Nat) (h1 : a + 400 < b) (h2 : b * 2 < c + 1200) (h3 : c < d + 400) :
    a + 400 < d + 1600 + b := by omega

theorem omega_401 (a b c d : Nat) (h1 : a + 401 < b) (h2 : b * 2 < c + 1203) (h3 : c < d + 401) :
    a + 401 < d + 1604 + b := by omega

theorem omega_402 (a b c d : Nat) (h1 : a + 402 < b) (h2 : b * 2 < c + 1206) (h3 : c < d + 402) :
    a + 402 < d + 1608 + b := by omega

theorem omega_403 (a b c d : Nat) (h1 : a + 403 < b) (h2 : b * 2 < c + 1209) (h3 : c < d + 403) :
    a + 403 < d + 1612 + b := by omega

theorem omega_404 (a b c d : Nat) (h1 : a + 404 < b) (h2 : b * 2 < c + 1212) (h3 : c < d + 404) :
    a + 404 < d + 1616 + b := by omega

theorem omega_405 (a b c d : Nat) (h1 : a + 405 < b) (h2 : b * 2 < c + 1215) (h3 : c < d + 405) :
    a + 405 < d + 1620 + b := by omega

theorem omega_406 (a b c d : Nat) (h1 : a + 406 < b) (h2 : b * 2 < c + 1218) (h3 : c < d + 406) :
    a + 406 < d + 1624 + b := by omega

theorem omega_407 (a b c d : Nat) (h1 : a + 407 < b) (h2 : b * 2 < c + 1221) (h3 : c < d + 407) :
    a + 407 < d + 1628 + b := by omega

theorem omega_408 (a b c d : Nat) (h1 : a + 408 < b) (h2 : b * 2 < c + 1224) (h3 : c < d + 408) :
    a + 408 < d + 1632 + b := by omega

theorem omega_409 (a b c d : Nat) (h1 : a + 409 < b) (h2 : b * 2 < c + 1227) (h3 : c < d + 409) :
    a + 409 < d + 1636 + b := by omega

theorem omega_410 (a b c d : Nat) (h1 : a + 410 < b) (h2 : b * 2 < c + 1230) (h3 : c < d + 410) :
    a + 410 < d + 1640 + b := by omega

theorem omega_411 (a b c d : Nat) (h1 : a + 411 < b) (h2 : b * 2 < c + 1233) (h3 : c < d + 411) :
    a + 411 < d + 1644 + b := by omega

theorem omega_412 (a b c d : Nat) (h1 : a + 412 < b) (h2 : b * 2 < c + 1236) (h3 : c < d + 412) :
    a + 412 < d + 1648 + b := by omega

theorem omega_413 (a b c d : Nat) (h1 : a + 413 < b) (h2 : b * 2 < c + 1239) (h3 : c < d + 413) :
    a + 413 < d + 1652 + b := by omega

theorem omega_414 (a b c d : Nat) (h1 : a + 414 < b) (h2 : b * 2 < c + 1242) (h3 : c < d + 414) :
    a + 414 < d + 1656 + b := by omega

theorem omega_415 (a b c d : Nat) (h1 : a + 415 < b) (h2 : b * 2 < c + 1245) (h3 : c < d + 415) :
    a + 415 < d + 1660 + b := by omega

theorem omega_416 (a b c d : Nat) (h1 : a + 416 < b) (h2 : b * 2 < c + 1248) (h3 : c < d + 416) :
    a + 416 < d + 1664 + b := by omega

theorem omega_417 (a b c d : Nat) (h1 : a + 417 < b) (h2 : b * 2 < c + 1251) (h3 : c < d + 417) :
    a + 417 < d + 1668 + b := by omega

theorem omega_418 (a b c d : Nat) (h1 : a + 418 < b) (h2 : b * 2 < c + 1254) (h3 : c < d + 418) :
    a + 418 < d + 1672 + b := by omega

theorem omega_419 (a b c d : Nat) (h1 : a + 419 < b) (h2 : b * 2 < c + 1257) (h3 : c < d + 419) :
    a + 419 < d + 1676 + b := by omega

theorem omega_420 (a b c d : Nat) (h1 : a + 420 < b) (h2 : b * 2 < c + 1260) (h3 : c < d + 420) :
    a + 420 < d + 1680 + b := by omega

theorem omega_421 (a b c d : Nat) (h1 : a + 421 < b) (h2 : b * 2 < c + 1263) (h3 : c < d + 421) :
    a + 421 < d + 1684 + b := by omega

theorem omega_422 (a b c d : Nat) (h1 : a + 422 < b) (h2 : b * 2 < c + 1266) (h3 : c < d + 422) :
    a + 422 < d + 1688 + b := by omega

theorem omega_423 (a b c d : Nat) (h1 : a + 423 < b) (h2 : b * 2 < c + 1269) (h3 : c < d + 423) :
    a + 423 < d + 1692 + b := by omega

theorem omega_424 (a b c d : Nat) (h1 : a + 424 < b) (h2 : b * 2 < c + 1272) (h3 : c < d + 424) :
    a + 424 < d + 1696 + b := by omega

theorem omega_425 (a b c d : Nat) (h1 : a + 425 < b) (h2 : b * 2 < c + 1275) (h3 : c < d + 425) :
    a + 425 < d + 1700 + b := by omega

theorem omega_426 (a b c d : Nat) (h1 : a + 426 < b) (h2 : b * 2 < c + 1278) (h3 : c < d + 426) :
    a + 426 < d + 1704 + b := by omega

theorem omega_427 (a b c d : Nat) (h1 : a + 427 < b) (h2 : b * 2 < c + 1281) (h3 : c < d + 427) :
    a + 427 < d + 1708 + b := by omega

theorem omega_428 (a b c d : Nat) (h1 : a + 428 < b) (h2 : b * 2 < c + 1284) (h3 : c < d + 428) :
    a + 428 < d + 1712 + b := by omega

theorem omega_429 (a b c d : Nat) (h1 : a + 429 < b) (h2 : b * 2 < c + 1287) (h3 : c < d + 429) :
    a + 429 < d + 1716 + b := by omega

theorem omega_430 (a b c d : Nat) (h1 : a + 430 < b) (h2 : b * 2 < c + 1290) (h3 : c < d + 430) :
    a + 430 < d + 1720 + b := by omega

theorem omega_431 (a b c d : Nat) (h1 : a + 431 < b) (h2 : b * 2 < c + 1293) (h3 : c < d + 431) :
    a + 431 < d + 1724 + b := by omega

theorem omega_432 (a b c d : Nat) (h1 : a + 432 < b) (h2 : b * 2 < c + 1296) (h3 : c < d + 432) :
    a + 432 < d + 1728 + b := by omega

theorem omega_433 (a b c d : Nat) (h1 : a + 433 < b) (h2 : b * 2 < c + 1299) (h3 : c < d + 433) :
    a + 433 < d + 1732 + b := by omega

theorem omega_434 (a b c d : Nat) (h1 : a + 434 < b) (h2 : b * 2 < c + 1302) (h3 : c < d + 434) :
    a + 434 < d + 1736 + b := by omega

theorem omega_435 (a b c d : Nat) (h1 : a + 435 < b) (h2 : b * 2 < c + 1305) (h3 : c < d + 435) :
    a + 435 < d + 1740 + b := by omega

theorem omega_436 (a b c d : Nat) (h1 : a + 436 < b) (h2 : b * 2 < c + 1308) (h3 : c < d + 436) :
    a + 436 < d + 1744 + b := by omega

theorem omega_437 (a b c d : Nat) (h1 : a + 437 < b) (h2 : b * 2 < c + 1311) (h3 : c < d + 437) :
    a + 437 < d + 1748 + b := by omega

theorem omega_438 (a b c d : Nat) (h1 : a + 438 < b) (h2 : b * 2 < c + 1314) (h3 : c < d + 438) :
    a + 438 < d + 1752 + b := by omega

theorem omega_439 (a b c d : Nat) (h1 : a + 439 < b) (h2 : b * 2 < c + 1317) (h3 : c < d + 439) :
    a + 439 < d + 1756 + b := by omega

theorem omega_440 (a b c d : Nat) (h1 : a + 440 < b) (h2 : b * 2 < c + 1320) (h3 : c < d + 440) :
    a + 440 < d + 1760 + b := by omega

theorem omega_441 (a b c d : Nat) (h1 : a + 441 < b) (h2 : b * 2 < c + 1323) (h3 : c < d + 441) :
    a + 441 < d + 1764 + b := by omega

theorem omega_442 (a b c d : Nat) (h1 : a + 442 < b) (h2 : b * 2 < c + 1326) (h3 : c < d + 442) :
    a + 442 < d + 1768 + b := by omega

theorem omega_443 (a b c d : Nat) (h1 : a + 443 < b) (h2 : b * 2 < c + 1329) (h3 : c < d + 443) :
    a + 443 < d + 1772 + b := by omega

theorem omega_444 (a b c d : Nat) (h1 : a + 444 < b) (h2 : b * 2 < c + 1332) (h3 : c < d + 444) :
    a + 444 < d + 1776 + b := by omega

theorem omega_445 (a b c d : Nat) (h1 : a + 445 < b) (h2 : b * 2 < c + 1335) (h3 : c < d + 445) :
    a + 445 < d + 1780 + b := by omega

theorem omega_446 (a b c d : Nat) (h1 : a + 446 < b) (h2 : b * 2 < c + 1338) (h3 : c < d + 446) :
    a + 446 < d + 1784 + b := by omega

theorem omega_447 (a b c d : Nat) (h1 : a + 447 < b) (h2 : b * 2 < c + 1341) (h3 : c < d + 447) :
    a + 447 < d + 1788 + b := by omega

theorem omega_448 (a b c d : Nat) (h1 : a + 448 < b) (h2 : b * 2 < c + 1344) (h3 : c < d + 448) :
    a + 448 < d + 1792 + b := by omega

theorem omega_449 (a b c d : Nat) (h1 : a + 449 < b) (h2 : b * 2 < c + 1347) (h3 : c < d + 449) :
    a + 449 < d + 1796 + b := by omega

theorem omega_450 (a b c d : Nat) (h1 : a + 450 < b) (h2 : b * 2 < c + 1350) (h3 : c < d + 450) :
    a + 450 < d + 1800 + b := by omega

theorem omega_451 (a b c d : Nat) (h1 : a + 451 < b) (h2 : b * 2 < c + 1353) (h3 : c < d + 451) :
    a + 451 < d + 1804 + b := by omega

theorem omega_452 (a b c d : Nat) (h1 : a + 452 < b) (h2 : b * 2 < c + 1356) (h3 : c < d + 452) :
    a + 452 < d + 1808 + b := by omega

theorem omega_453 (a b c d : Nat) (h1 : a + 453 < b) (h2 : b * 2 < c + 1359) (h3 : c < d + 453) :
    a + 453 < d + 1812 + b := by omega

theorem omega_454 (a b c d : Nat) (h1 : a + 454 < b) (h2 : b * 2 < c + 1362) (h3 : c < d + 454) :
    a + 454 < d + 1816 + b := by omega

theorem omega_455 (a b c d : Nat) (h1 : a + 455 < b) (h2 : b * 2 < c + 1365) (h3 : c < d + 455) :
    a + 455 < d + 1820 + b := by omega

theorem omega_456 (a b c d : Nat) (h1 : a + 456 < b) (h2 : b * 2 < c + 1368) (h3 : c < d + 456) :
    a + 456 < d + 1824 + b := by omega

theorem omega_457 (a b c d : Nat) (h1 : a + 457 < b) (h2 : b * 2 < c + 1371) (h3 : c < d + 457) :
    a + 457 < d + 1828 + b := by omega

theorem omega_458 (a b c d : Nat) (h1 : a + 458 < b) (h2 : b * 2 < c + 1374) (h3 : c < d + 458) :
    a + 458 < d + 1832 + b := by omega

theorem omega_459 (a b c d : Nat) (h1 : a + 459 < b) (h2 : b * 2 < c + 1377) (h3 : c < d + 459) :
    a + 459 < d + 1836 + b := by omega

theorem omega_460 (a b c d : Nat) (h1 : a + 460 < b) (h2 : b * 2 < c + 1380) (h3 : c < d + 460) :
    a + 460 < d + 1840 + b := by omega

theorem omega_461 (a b c d : Nat) (h1 : a + 461 < b) (h2 : b * 2 < c + 1383) (h3 : c < d + 461) :
    a + 461 < d + 1844 + b := by omega

theorem omega_462 (a b c d : Nat) (h1 : a + 462 < b) (h2 : b * 2 < c + 1386) (h3 : c < d + 462) :
    a + 462 < d + 1848 + b := by omega

theorem omega_463 (a b c d : Nat) (h1 : a + 463 < b) (h2 : b * 2 < c + 1389) (h3 : c < d + 463) :
    a + 463 < d + 1852 + b := by omega

theorem omega_464 (a b c d : Nat) (h1 : a + 464 < b) (h2 : b * 2 < c + 1392) (h3 : c < d + 464) :
    a + 464 < d + 1856 + b := by omega

theorem omega_465 (a b c d : Nat) (h1 : a + 465 < b) (h2 : b * 2 < c + 1395) (h3 : c < d + 465) :
    a + 465 < d + 1860 + b := by omega

theorem omega_466 (a b c d : Nat) (h1 : a + 466 < b) (h2 : b * 2 < c + 1398) (h3 : c < d + 466) :
    a + 466 < d + 1864 + b := by omega

theorem omega_467 (a b c d : Nat) (h1 : a + 467 < b) (h2 : b * 2 < c + 1401) (h3 : c < d + 467) :
    a + 467 < d + 1868 + b := by omega

theorem omega_468 (a b c d : Nat) (h1 : a + 468 < b) (h2 : b * 2 < c + 1404) (h3 : c < d + 468) :
    a + 468 < d + 1872 + b := by omega

theorem omega_469 (a b c d : Nat) (h1 : a + 469 < b) (h2 : b * 2 < c + 1407) (h3 : c < d + 469) :
    a + 469 < d + 1876 + b := by omega

theorem omega_470 (a b c d : Nat) (h1 : a + 470 < b) (h2 : b * 2 < c + 1410) (h3 : c < d + 470) :
    a + 470 < d + 1880 + b := by omega

theorem omega_471 (a b c d : Nat) (h1 : a + 471 < b) (h2 : b * 2 < c + 1413) (h3 : c < d + 471) :
    a + 471 < d + 1884 + b := by omega

theorem omega_472 (a b c d : Nat) (h1 : a + 472 < b) (h2 : b * 2 < c + 1416) (h3 : c < d + 472) :
    a + 472 < d + 1888 + b := by omega

theorem omega_473 (a b c d : Nat) (h1 : a + 473 < b) (h2 : b * 2 < c + 1419) (h3 : c < d + 473) :
    a + 473 < d + 1892 + b := by omega

theorem omega_474 (a b c d : Nat) (h1 : a + 474 < b) (h2 : b * 2 < c + 1422) (h3 : c < d + 474) :
    a + 474 < d + 1896 + b := by omega

theorem omega_475 (a b c d : Nat) (h1 : a + 475 < b) (h2 : b * 2 < c + 1425) (h3 : c < d + 475) :
    a + 475 < d + 1900 + b := by omega

theorem omega_476 (a b c d : Nat) (h1 : a + 476 < b) (h2 : b * 2 < c + 1428) (h3 : c < d + 476) :
    a + 476 < d + 1904 + b := by omega

theorem omega_477 (a b c d : Nat) (h1 : a + 477 < b) (h2 : b * 2 < c + 1431) (h3 : c < d + 477) :
    a + 477 < d + 1908 + b := by omega

theorem omega_478 (a b c d : Nat) (h1 : a + 478 < b) (h2 : b * 2 < c + 1434) (h3 : c < d + 478) :
    a + 478 < d + 1912 + b := by omega

theorem omega_479 (a b c d : Nat) (h1 : a + 479 < b) (h2 : b * 2 < c + 1437) (h3 : c < d + 479) :
    a + 479 < d + 1916 + b := by omega

theorem omega_480 (a b c d : Nat) (h1 : a + 480 < b) (h2 : b * 2 < c + 1440) (h3 : c < d + 480) :
    a + 480 < d + 1920 + b := by omega

theorem omega_481 (a b c d : Nat) (h1 : a + 481 < b) (h2 : b * 2 < c + 1443) (h3 : c < d + 481) :
    a + 481 < d + 1924 + b := by omega

theorem omega_482 (a b c d : Nat) (h1 : a + 482 < b) (h2 : b * 2 < c + 1446) (h3 : c < d + 482) :
    a + 482 < d + 1928 + b := by omega

theorem omega_483 (a b c d : Nat) (h1 : a + 483 < b) (h2 : b * 2 < c + 1449) (h3 : c < d + 483) :
    a + 483 < d + 1932 + b := by omega

theorem omega_484 (a b c d : Nat) (h1 : a + 484 < b) (h2 : b * 2 < c + 1452) (h3 : c < d + 484) :
    a + 484 < d + 1936 + b := by omega

theorem omega_485 (a b c d : Nat) (h1 : a + 485 < b) (h2 : b * 2 < c + 1455) (h3 : c < d + 485) :
    a + 485 < d + 1940 + b := by omega

theorem omega_486 (a b c d : Nat) (h1 : a + 486 < b) (h2 : b * 2 < c + 1458) (h3 : c < d + 486) :
    a + 486 < d + 1944 + b := by omega

theorem omega_487 (a b c d : Nat) (h1 : a + 487 < b) (h2 : b * 2 < c + 1461) (h3 : c < d + 487) :
    a + 487 < d + 1948 + b := by omega

theorem omega_488 (a b c d : Nat) (h1 : a + 488 < b) (h2 : b * 2 < c + 1464) (h3 : c < d + 488) :
    a + 488 < d + 1952 + b := by omega

theorem omega_489 (a b c d : Nat) (h1 : a + 489 < b) (h2 : b * 2 < c + 1467) (h3 : c < d + 489) :
    a + 489 < d + 1956 + b := by omega

theorem omega_490 (a b c d : Nat) (h1 : a + 490 < b) (h2 : b * 2 < c + 1470) (h3 : c < d + 490) :
    a + 490 < d + 1960 + b := by omega

theorem omega_491 (a b c d : Nat) (h1 : a + 491 < b) (h2 : b * 2 < c + 1473) (h3 : c < d + 491) :
    a + 491 < d + 1964 + b := by omega

theorem omega_492 (a b c d : Nat) (h1 : a + 492 < b) (h2 : b * 2 < c + 1476) (h3 : c < d + 492) :
    a + 492 < d + 1968 + b := by omega

theorem omega_493 (a b c d : Nat) (h1 : a + 493 < b) (h2 : b * 2 < c + 1479) (h3 : c < d + 493) :
    a + 493 < d + 1972 + b := by omega

theorem omega_494 (a b c d : Nat) (h1 : a + 494 < b) (h2 : b * 2 < c + 1482) (h3 : c < d + 494) :
    a + 494 < d + 1976 + b := by omega

theorem omega_495 (a b c d : Nat) (h1 : a + 495 < b) (h2 : b * 2 < c + 1485) (h3 : c < d + 495) :
    a + 495 < d + 1980 + b := by omega

theorem omega_496 (a b c d : Nat) (h1 : a + 496 < b) (h2 : b * 2 < c + 1488) (h3 : c < d + 496) :
    a + 496 < d + 1984 + b := by omega

theorem omega_497 (a b c d : Nat) (h1 : a + 497 < b) (h2 : b * 2 < c + 1491) (h3 : c < d + 497) :
    a + 497 < d + 1988 + b := by omega

theorem omega_498 (a b c d : Nat) (h1 : a + 498 < b) (h2 : b * 2 < c + 1494) (h3 : c < d + 498) :
    a + 498 < d + 1992 + b := by omega

theorem omega_499 (a b c d : Nat) (h1 : a + 499 < b) (h2 : b * 2 < c + 1497) (h3 : c < d + 499) :
    a + 499 < d + 1996 + b := by omega

theorem omega_500 (a b c d : Nat) (h1 : a + 500 < b) (h2 : b * 2 < c + 1500) (h3 : c < d + 500) :
    a + 500 < d + 2000 + b := by omega

theorem omega_501 (a b c d : Nat) (h1 : a + 501 < b) (h2 : b * 2 < c + 1503) (h3 : c < d + 501) :
    a + 501 < d + 2004 + b := by omega

theorem omega_502 (a b c d : Nat) (h1 : a + 502 < b) (h2 : b * 2 < c + 1506) (h3 : c < d + 502) :
    a + 502 < d + 2008 + b := by omega

theorem omega_503 (a b c d : Nat) (h1 : a + 503 < b) (h2 : b * 2 < c + 1509) (h3 : c < d + 503) :
    a + 503 < d + 2012 + b := by omega

theorem omega_504 (a b c d : Nat) (h1 : a + 504 < b) (h2 : b * 2 < c + 1512) (h3 : c < d + 504) :
    a + 504 < d + 2016 + b := by omega

theorem omega_505 (a b c d : Nat) (h1 : a + 505 < b) (h2 : b * 2 < c + 1515) (h3 : c < d + 505) :
    a + 505 < d + 2020 + b := by omega

theorem omega_506 (a b c d : Nat) (h1 : a + 506 < b) (h2 : b * 2 < c + 1518) (h3 : c < d + 506) :
    a + 506 < d + 2024 + b := by omega

theorem omega_507 (a b c d : Nat) (h1 : a + 507 < b) (h2 : b * 2 < c + 1521) (h3 : c < d + 507) :
    a + 507 < d + 2028 + b := by omega

theorem omega_508 (a b c d : Nat) (h1 : a + 508 < b) (h2 : b * 2 < c + 1524) (h3 : c < d + 508) :
    a + 508 < d + 2032 + b := by omega

theorem omega_509 (a b c d : Nat) (h1 : a + 509 < b) (h2 : b * 2 < c + 1527) (h3 : c < d + 509) :
    a + 509 < d + 2036 + b := by omega

theorem omega_510 (a b c d : Nat) (h1 : a + 510 < b) (h2 : b * 2 < c + 1530) (h3 : c < d + 510) :
    a + 510 < d + 2040 + b := by omega

theorem omega_511 (a b c d : Nat) (h1 : a + 511 < b) (h2 : b * 2 < c + 1533) (h3 : c < d + 511) :
    a + 511 < d + 2044 + b := by omega

theorem omega_512 (a b c d : Nat) (h1 : a + 512 < b) (h2 : b * 2 < c + 1536) (h3 : c < d + 512) :
    a + 512 < d + 2048 + b := by omega

theorem omega_513 (a b c d : Nat) (h1 : a + 513 < b) (h2 : b * 2 < c + 1539) (h3 : c < d + 513) :
    a + 513 < d + 2052 + b := by omega

theorem omega_514 (a b c d : Nat) (h1 : a + 514 < b) (h2 : b * 2 < c + 1542) (h3 : c < d + 514) :
    a + 514 < d + 2056 + b := by omega

theorem omega_515 (a b c d : Nat) (h1 : a + 515 < b) (h2 : b * 2 < c + 1545) (h3 : c < d + 515) :
    a + 515 < d + 2060 + b := by omega

theorem omega_516 (a b c d : Nat) (h1 : a + 516 < b) (h2 : b * 2 < c + 1548) (h3 : c < d + 516) :
    a + 516 < d + 2064 + b := by omega

theorem omega_517 (a b c d : Nat) (h1 : a + 517 < b) (h2 : b * 2 < c + 1551) (h3 : c < d + 517) :
    a + 517 < d + 2068 + b := by omega

theorem omega_518 (a b c d : Nat) (h1 : a + 518 < b) (h2 : b * 2 < c + 1554) (h3 : c < d + 518) :
    a + 518 < d + 2072 + b := by omega

theorem omega_519 (a b c d : Nat) (h1 : a + 519 < b) (h2 : b * 2 < c + 1557) (h3 : c < d + 519) :
    a + 519 < d + 2076 + b := by omega

theorem omega_520 (a b c d : Nat) (h1 : a + 520 < b) (h2 : b * 2 < c + 1560) (h3 : c < d + 520) :
    a + 520 < d + 2080 + b := by omega

theorem omega_521 (a b c d : Nat) (h1 : a + 521 < b) (h2 : b * 2 < c + 1563) (h3 : c < d + 521) :
    a + 521 < d + 2084 + b := by omega

theorem omega_522 (a b c d : Nat) (h1 : a + 522 < b) (h2 : b * 2 < c + 1566) (h3 : c < d + 522) :
    a + 522 < d + 2088 + b := by omega

theorem omega_523 (a b c d : Nat) (h1 : a + 523 < b) (h2 : b * 2 < c + 1569) (h3 : c < d + 523) :
    a + 523 < d + 2092 + b := by omega

theorem omega_524 (a b c d : Nat) (h1 : a + 524 < b) (h2 : b * 2 < c + 1572) (h3 : c < d + 524) :
    a + 524 < d + 2096 + b := by omega

theorem omega_525 (a b c d : Nat) (h1 : a + 525 < b) (h2 : b * 2 < c + 1575) (h3 : c < d + 525) :
    a + 525 < d + 2100 + b := by omega

theorem omega_526 (a b c d : Nat) (h1 : a + 526 < b) (h2 : b * 2 < c + 1578) (h3 : c < d + 526) :
    a + 526 < d + 2104 + b := by omega

theorem omega_527 (a b c d : Nat) (h1 : a + 527 < b) (h2 : b * 2 < c + 1581) (h3 : c < d + 527) :
    a + 527 < d + 2108 + b := by omega

theorem omega_528 (a b c d : Nat) (h1 : a + 528 < b) (h2 : b * 2 < c + 1584) (h3 : c < d + 528) :
    a + 528 < d + 2112 + b := by omega

theorem omega_529 (a b c d : Nat) (h1 : a + 529 < b) (h2 : b * 2 < c + 1587) (h3 : c < d + 529) :
    a + 529 < d + 2116 + b := by omega

theorem omega_530 (a b c d : Nat) (h1 : a + 530 < b) (h2 : b * 2 < c + 1590) (h3 : c < d + 530) :
    a + 530 < d + 2120 + b := by omega

theorem omega_531 (a b c d : Nat) (h1 : a + 531 < b) (h2 : b * 2 < c + 1593) (h3 : c < d + 531) :
    a + 531 < d + 2124 + b := by omega

theorem omega_532 (a b c d : Nat) (h1 : a + 532 < b) (h2 : b * 2 < c + 1596) (h3 : c < d + 532) :
    a + 532 < d + 2128 + b := by omega

theorem omega_533 (a b c d : Nat) (h1 : a + 533 < b) (h2 : b * 2 < c + 1599) (h3 : c < d + 533) :
    a + 533 < d + 2132 + b := by omega

theorem omega_534 (a b c d : Nat) (h1 : a + 534 < b) (h2 : b * 2 < c + 1602) (h3 : c < d + 534) :
    a + 534 < d + 2136 + b := by omega

theorem omega_535 (a b c d : Nat) (h1 : a + 535 < b) (h2 : b * 2 < c + 1605) (h3 : c < d + 535) :
    a + 535 < d + 2140 + b := by omega

theorem omega_536 (a b c d : Nat) (h1 : a + 536 < b) (h2 : b * 2 < c + 1608) (h3 : c < d + 536) :
    a + 536 < d + 2144 + b := by omega

theorem omega_537 (a b c d : Nat) (h1 : a + 537 < b) (h2 : b * 2 < c + 1611) (h3 : c < d + 537) :
    a + 537 < d + 2148 + b := by omega

theorem omega_538 (a b c d : Nat) (h1 : a + 538 < b) (h2 : b * 2 < c + 1614) (h3 : c < d + 538) :
    a + 538 < d + 2152 + b := by omega

theorem omega_539 (a b c d : Nat) (h1 : a + 539 < b) (h2 : b * 2 < c + 1617) (h3 : c < d + 539) :
    a + 539 < d + 2156 + b := by omega

theorem omega_540 (a b c d : Nat) (h1 : a + 540 < b) (h2 : b * 2 < c + 1620) (h3 : c < d + 540) :
    a + 540 < d + 2160 + b := by omega

theorem omega_541 (a b c d : Nat) (h1 : a + 541 < b) (h2 : b * 2 < c + 1623) (h3 : c < d + 541) :
    a + 541 < d + 2164 + b := by omega

theorem omega_542 (a b c d : Nat) (h1 : a + 542 < b) (h2 : b * 2 < c + 1626) (h3 : c < d + 542) :
    a + 542 < d + 2168 + b := by omega

theorem omega_543 (a b c d : Nat) (h1 : a + 543 < b) (h2 : b * 2 < c + 1629) (h3 : c < d + 543) :
    a + 543 < d + 2172 + b := by omega

theorem omega_544 (a b c d : Nat) (h1 : a + 544 < b) (h2 : b * 2 < c + 1632) (h3 : c < d + 544) :
    a + 544 < d + 2176 + b := by omega

theorem omega_545 (a b c d : Nat) (h1 : a + 545 < b) (h2 : b * 2 < c + 1635) (h3 : c < d + 545) :
    a + 545 < d + 2180 + b := by omega

theorem omega_546 (a b c d : Nat) (h1 : a + 546 < b) (h2 : b * 2 < c + 1638) (h3 : c < d + 546) :
    a + 546 < d + 2184 + b := by omega

theorem omega_547 (a b c d : Nat) (h1 : a + 547 < b) (h2 : b * 2 < c + 1641) (h3 : c < d + 547) :
    a + 547 < d + 2188 + b := by omega

theorem omega_548 (a b c d : Nat) (h1 : a + 548 < b) (h2 : b * 2 < c + 1644) (h3 : c < d + 548) :
    a + 548 < d + 2192 + b := by omega

theorem omega_549 (a b c d : Nat) (h1 : a + 549 < b) (h2 : b * 2 < c + 1647) (h3 : c < d + 549) :
    a + 549 < d + 2196 + b := by omega

theorem omega_550 (a b c d : Nat) (h1 : a + 550 < b) (h2 : b * 2 < c + 1650) (h3 : c < d + 550) :
    a + 550 < d + 2200 + b := by omega

theorem omega_551 (a b c d : Nat) (h1 : a + 551 < b) (h2 : b * 2 < c + 1653) (h3 : c < d + 551) :
    a + 551 < d + 2204 + b := by omega

theorem omega_552 (a b c d : Nat) (h1 : a + 552 < b) (h2 : b * 2 < c + 1656) (h3 : c < d + 552) :
    a + 552 < d + 2208 + b := by omega

theorem omega_553 (a b c d : Nat) (h1 : a + 553 < b) (h2 : b * 2 < c + 1659) (h3 : c < d + 553) :
    a + 553 < d + 2212 + b := by omega

theorem omega_554 (a b c d : Nat) (h1 : a + 554 < b) (h2 : b * 2 < c + 1662) (h3 : c < d + 554) :
    a + 554 < d + 2216 + b := by omega

theorem omega_555 (a b c d : Nat) (h1 : a + 555 < b) (h2 : b * 2 < c + 1665) (h3 : c < d + 555) :
    a + 555 < d + 2220 + b := by omega

theorem omega_556 (a b c d : Nat) (h1 : a + 556 < b) (h2 : b * 2 < c + 1668) (h3 : c < d + 556) :
    a + 556 < d + 2224 + b := by omega

theorem omega_557 (a b c d : Nat) (h1 : a + 557 < b) (h2 : b * 2 < c + 1671) (h3 : c < d + 557) :
    a + 557 < d + 2228 + b := by omega

theorem omega_558 (a b c d : Nat) (h1 : a + 558 < b) (h2 : b * 2 < c + 1674) (h3 : c < d + 558) :
    a + 558 < d + 2232 + b := by omega

theorem omega_559 (a b c d : Nat) (h1 : a + 559 < b) (h2 : b * 2 < c + 1677) (h3 : c < d + 559) :
    a + 559 < d + 2236 + b := by omega

theorem omega_560 (a b c d : Nat) (h1 : a + 560 < b) (h2 : b * 2 < c + 1680) (h3 : c < d + 560) :
    a + 560 < d + 2240 + b := by omega

theorem omega_561 (a b c d : Nat) (h1 : a + 561 < b) (h2 : b * 2 < c + 1683) (h3 : c < d + 561) :
    a + 561 < d + 2244 + b := by omega

theorem omega_562 (a b c d : Nat) (h1 : a + 562 < b) (h2 : b * 2 < c + 1686) (h3 : c < d + 562) :
    a + 562 < d + 2248 + b := by omega

theorem omega_563 (a b c d : Nat) (h1 : a + 563 < b) (h2 : b * 2 < c + 1689) (h3 : c < d + 563) :
    a + 563 < d + 2252 + b := by omega

theorem omega_564 (a b c d : Nat) (h1 : a + 564 < b) (h2 : b * 2 < c + 1692) (h3 : c < d + 564) :
    a + 564 < d + 2256 + b := by omega

theorem omega_565 (a b c d : Nat) (h1 : a + 565 < b) (h2 : b * 2 < c + 1695) (h3 : c < d + 565) :
    a + 565 < d + 2260 + b := by omega

theorem omega_566 (a b c d : Nat) (h1 : a + 566 < b) (h2 : b * 2 < c + 1698) (h3 : c < d + 566) :
    a + 566 < d + 2264 + b := by omega

theorem omega_567 (a b c d : Nat) (h1 : a + 567 < b) (h2 : b * 2 < c + 1701) (h3 : c < d + 567) :
    a + 567 < d + 2268 + b := by omega

theorem omega_568 (a b c d : Nat) (h1 : a + 568 < b) (h2 : b * 2 < c + 1704) (h3 : c < d + 568) :
    a + 568 < d + 2272 + b := by omega

theorem omega_569 (a b c d : Nat) (h1 : a + 569 < b) (h2 : b * 2 < c + 1707) (h3 : c < d + 569) :
    a + 569 < d + 2276 + b := by omega

theorem omega_570 (a b c d : Nat) (h1 : a + 570 < b) (h2 : b * 2 < c + 1710) (h3 : c < d + 570) :
    a + 570 < d + 2280 + b := by omega

theorem omega_571 (a b c d : Nat) (h1 : a + 571 < b) (h2 : b * 2 < c + 1713) (h3 : c < d + 571) :
    a + 571 < d + 2284 + b := by omega

theorem omega_572 (a b c d : Nat) (h1 : a + 572 < b) (h2 : b * 2 < c + 1716) (h3 : c < d + 572) :
    a + 572 < d + 2288 + b := by omega

theorem omega_573 (a b c d : Nat) (h1 : a + 573 < b) (h2 : b * 2 < c + 1719) (h3 : c < d + 573) :
    a + 573 < d + 2292 + b := by omega

theorem omega_574 (a b c d : Nat) (h1 : a + 574 < b) (h2 : b * 2 < c + 1722) (h3 : c < d + 574) :
    a + 574 < d + 2296 + b := by omega

theorem omega_575 (a b c d : Nat) (h1 : a + 575 < b) (h2 : b * 2 < c + 1725) (h3 : c < d + 575) :
    a + 575 < d + 2300 + b := by omega

theorem omega_576 (a b c d : Nat) (h1 : a + 576 < b) (h2 : b * 2 < c + 1728) (h3 : c < d + 576) :
    a + 576 < d + 2304 + b := by omega

theorem omega_577 (a b c d : Nat) (h1 : a + 577 < b) (h2 : b * 2 < c + 1731) (h3 : c < d + 577) :
    a + 577 < d + 2308 + b := by omega

theorem omega_578 (a b c d : Nat) (h1 : a + 578 < b) (h2 : b * 2 < c + 1734) (h3 : c < d + 578) :
    a + 578 < d + 2312 + b := by omega

theorem omega_579 (a b c d : Nat) (h1 : a + 579 < b) (h2 : b * 2 < c + 1737) (h3 : c < d + 579) :
    a + 579 < d + 2316 + b := by omega

theorem omega_580 (a b c d : Nat) (h1 : a + 580 < b) (h2 : b * 2 < c + 1740) (h3 : c < d + 580) :
    a + 580 < d + 2320 + b := by omega

theorem omega_581 (a b c d : Nat) (h1 : a + 581 < b) (h2 : b * 2 < c + 1743) (h3 : c < d + 581) :
    a + 581 < d + 2324 + b := by omega

theorem omega_582 (a b c d : Nat) (h1 : a + 582 < b) (h2 : b * 2 < c + 1746) (h3 : c < d + 582) :
    a + 582 < d + 2328 + b := by omega

theorem omega_583 (a b c d : Nat) (h1 : a + 583 < b) (h2 : b * 2 < c + 1749) (h3 : c < d + 583) :
    a + 583 < d + 2332 + b := by omega

theorem omega_584 (a b c d : Nat) (h1 : a + 584 < b) (h2 : b * 2 < c + 1752) (h3 : c < d + 584) :
    a + 584 < d + 2336 + b := by omega

theorem omega_585 (a b c d : Nat) (h1 : a + 585 < b) (h2 : b * 2 < c + 1755) (h3 : c < d + 585) :
    a + 585 < d + 2340 + b := by omega

theorem omega_586 (a b c d : Nat) (h1 : a + 586 < b) (h2 : b * 2 < c + 1758) (h3 : c < d + 586) :
    a + 586 < d + 2344 + b := by omega

theorem omega_587 (a b c d : Nat) (h1 : a + 587 < b) (h2 : b * 2 < c + 1761) (h3 : c < d + 587) :
    a + 587 < d + 2348 + b := by omega

theorem omega_588 (a b c d : Nat) (h1 : a + 588 < b) (h2 : b * 2 < c + 1764) (h3 : c < d + 588) :
    a + 588 < d + 2352 + b := by omega

theorem omega_589 (a b c d : Nat) (h1 : a + 589 < b) (h2 : b * 2 < c + 1767) (h3 : c < d + 589) :
    a + 589 < d + 2356 + b := by omega

theorem omega_590 (a b c d : Nat) (h1 : a + 590 < b) (h2 : b * 2 < c + 1770) (h3 : c < d + 590) :
    a + 590 < d + 2360 + b := by omega

theorem omega_591 (a b c d : Nat) (h1 : a + 591 < b) (h2 : b * 2 < c + 1773) (h3 : c < d + 591) :
    a + 591 < d + 2364 + b := by omega

theorem omega_592 (a b c d : Nat) (h1 : a + 592 < b) (h2 : b * 2 < c + 1776) (h3 : c < d + 592) :
    a + 592 < d + 2368 + b := by omega

theorem omega_593 (a b c d : Nat) (h1 : a + 593 < b) (h2 : b * 2 < c + 1779) (h3 : c < d + 593) :
    a + 593 < d + 2372 + b := by omega

theorem omega_594 (a b c d : Nat) (h1 : a + 594 < b) (h2 : b * 2 < c + 1782) (h3 : c < d + 594) :
    a + 594 < d + 2376 + b := by omega

theorem omega_595 (a b c d : Nat) (h1 : a + 595 < b) (h2 : b * 2 < c + 1785) (h3 : c < d + 595) :
    a + 595 < d + 2380 + b := by omega

theorem omega_596 (a b c d : Nat) (h1 : a + 596 < b) (h2 : b * 2 < c + 1788) (h3 : c < d + 596) :
    a + 596 < d + 2384 + b := by omega

theorem omega_597 (a b c d : Nat) (h1 : a + 597 < b) (h2 : b * 2 < c + 1791) (h3 : c < d + 597) :
    a + 597 < d + 2388 + b := by omega

theorem omega_598 (a b c d : Nat) (h1 : a + 598 < b) (h2 : b * 2 < c + 1794) (h3 : c < d + 598) :
    a + 598 < d + 2392 + b := by omega

theorem omega_599 (a b c d : Nat) (h1 : a + 599 < b) (h2 : b * 2 < c + 1797) (h3 : c < d + 599) :
    a + 599 < d + 2396 + b := by omega

theorem omega_600 (a b c d : Nat) (h1 : a + 600 < b) (h2 : b * 2 < c + 1800) (h3 : c < d + 600) :
    a + 600 < d + 2400 + b := by omega

theorem simp_1 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 1 = zs.length + ys.length + xs.length + 1 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_2 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 2 = zs.length + ys.length + xs.length + 2 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_3 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 3 = zs.length + ys.length + xs.length + 3 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_4 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 4 = zs.length + ys.length + xs.length + 4 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_5 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 5 = zs.length + ys.length + xs.length + 5 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_6 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 6 = zs.length + ys.length + xs.length + 6 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_7 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 7 = zs.length + ys.length + xs.length + 7 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_8 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 8 = zs.length + ys.length + xs.length + 8 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_9 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 9 = zs.length + ys.length + xs.length + 9 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_10 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 10 = zs.length + ys.length + xs.length + 10 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_11 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 11 = zs.length + ys.length + xs.length + 11 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_12 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 12 = zs.length + ys.length + xs.length + 12 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_13 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 13 = zs.length + ys.length + xs.length + 13 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_14 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 14 = zs.length + ys.length + xs.length + 14 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_15 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 15 = zs.length + ys.length + xs.length + 15 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_16 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 16 = zs.length + ys.length + xs.length + 16 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_17 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 17 = zs.length + ys.length + xs.length + 17 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_18 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 18 = zs.length + ys.length + xs.length + 18 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_19 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 19 = zs.length + ys.length + xs.length + 19 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_20 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 20 = zs.length + ys.length + xs.length + 20 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_21 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 21 = zs.length + ys.length + xs.length + 21 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_22 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 22 = zs.length + ys.length + xs.length + 22 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_23 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 23 = zs.length + ys.length + xs.length + 23 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_24 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 24 = zs.length + ys.length + xs.length + 24 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_25 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 25 = zs.length + ys.length + xs.length + 25 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_26 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 26 = zs.length + ys.length + xs.length + 26 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_27 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 27 = zs.length + ys.length + xs.length + 27 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_28 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 28 = zs.length + ys.length + xs.length + 28 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_29 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 29 = zs.length + ys.length + xs.length + 29 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_30 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 30 = zs.length + ys.length + xs.length + 30 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_31 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 31 = zs.length + ys.length + xs.length + 31 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_32 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 32 = zs.length + ys.length + xs.length + 32 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_33 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 33 = zs.length + ys.length + xs.length + 33 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_34 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 34 = zs.length + ys.length + xs.length + 34 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_35 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 35 = zs.length + ys.length + xs.length + 35 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_36 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 36 = zs.length + ys.length + xs.length + 36 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_37 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 37 = zs.length + ys.length + xs.length + 37 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_38 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 38 = zs.length + ys.length + xs.length + 38 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_39 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 39 = zs.length + ys.length + xs.length + 39 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_40 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 40 = zs.length + ys.length + xs.length + 40 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_41 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 41 = zs.length + ys.length + xs.length + 41 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_42 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 42 = zs.length + ys.length + xs.length + 42 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_43 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 43 = zs.length + ys.length + xs.length + 43 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_44 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 44 = zs.length + ys.length + xs.length + 44 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_45 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 45 = zs.length + ys.length + xs.length + 45 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_46 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 46 = zs.length + ys.length + xs.length + 46 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_47 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 47 = zs.length + ys.length + xs.length + 47 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_48 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 48 = zs.length + ys.length + xs.length + 48 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_49 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 49 = zs.length + ys.length + xs.length + 49 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_50 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 50 = zs.length + ys.length + xs.length + 50 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_51 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 51 = zs.length + ys.length + xs.length + 51 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_52 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 52 = zs.length + ys.length + xs.length + 52 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_53 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 53 = zs.length + ys.length + xs.length + 53 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_54 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 54 = zs.length + ys.length + xs.length + 54 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_55 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 55 = zs.length + ys.length + xs.length + 55 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_56 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 56 = zs.length + ys.length + xs.length + 56 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_57 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 57 = zs.length + ys.length + xs.length + 57 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_58 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 58 = zs.length + ys.length + xs.length + 58 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_59 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 59 = zs.length + ys.length + xs.length + 59 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_60 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 60 = zs.length + ys.length + xs.length + 60 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_61 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 61 = zs.length + ys.length + xs.length + 61 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_62 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 62 = zs.length + ys.length + xs.length + 62 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_63 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 63 = zs.length + ys.length + xs.length + 63 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_64 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 64 = zs.length + ys.length + xs.length + 64 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_65 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 65 = zs.length + ys.length + xs.length + 65 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_66 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 66 = zs.length + ys.length + xs.length + 66 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_67 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 67 = zs.length + ys.length + xs.length + 67 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_68 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 68 = zs.length + ys.length + xs.length + 68 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_69 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 69 = zs.length + ys.length + xs.length + 69 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_70 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 70 = zs.length + ys.length + xs.length + 70 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_71 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 71 = zs.length + ys.length + xs.length + 71 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_72 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 72 = zs.length + ys.length + xs.length + 72 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_73 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 73 = zs.length + ys.length + xs.length + 73 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_74 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 74 = zs.length + ys.length + xs.length + 74 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_75 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 75 = zs.length + ys.length + xs.length + 75 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_76 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 76 = zs.length + ys.length + xs.length + 76 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_77 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 77 = zs.length + ys.length + xs.length + 77 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_78 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 78 = zs.length + ys.length + xs.length + 78 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_79 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 79 = zs.length + ys.length + xs.length + 79 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_80 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 80 = zs.length + ys.length + xs.length + 80 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_81 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 81 = zs.length + ys.length + xs.length + 81 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_82 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 82 = zs.length + ys.length + xs.length + 82 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_83 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 83 = zs.length + ys.length + xs.length + 83 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_84 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 84 = zs.length + ys.length + xs.length + 84 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_85 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 85 = zs.length + ys.length + xs.length + 85 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_86 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 86 = zs.length + ys.length + xs.length + 86 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_87 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 87 = zs.length + ys.length + xs.length + 87 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_88 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 88 = zs.length + ys.length + xs.length + 88 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_89 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 89 = zs.length + ys.length + xs.length + 89 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_90 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 90 = zs.length + ys.length + xs.length + 90 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_91 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 91 = zs.length + ys.length + xs.length + 91 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_92 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 92 = zs.length + ys.length + xs.length + 92 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_93 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 93 = zs.length + ys.length + xs.length + 93 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_94 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 94 = zs.length + ys.length + xs.length + 94 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_95 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 95 = zs.length + ys.length + xs.length + 95 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_96 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 96 = zs.length + ys.length + xs.length + 96 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_97 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 97 = zs.length + ys.length + xs.length + 97 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_98 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 98 = zs.length + ys.length + xs.length + 98 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_99 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 99 = zs.length + ys.length + xs.length + 99 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_100 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 100 = zs.length + ys.length + xs.length + 100 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_101 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 101 = zs.length + ys.length + xs.length + 101 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_102 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 102 = zs.length + ys.length + xs.length + 102 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_103 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 103 = zs.length + ys.length + xs.length + 103 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_104 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 104 = zs.length + ys.length + xs.length + 104 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_105 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 105 = zs.length + ys.length + xs.length + 105 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_106 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 106 = zs.length + ys.length + xs.length + 106 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_107 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 107 = zs.length + ys.length + xs.length + 107 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_108 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 108 = zs.length + ys.length + xs.length + 108 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_109 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 109 = zs.length + ys.length + xs.length + 109 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_110 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 110 = zs.length + ys.length + xs.length + 110 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_111 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 111 = zs.length + ys.length + xs.length + 111 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_112 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 112 = zs.length + ys.length + xs.length + 112 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_113 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 113 = zs.length + ys.length + xs.length + 113 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_114 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 114 = zs.length + ys.length + xs.length + 114 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_115 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 115 = zs.length + ys.length + xs.length + 115 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_116 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 116 = zs.length + ys.length + xs.length + 116 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_117 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 117 = zs.length + ys.length + xs.length + 117 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_118 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 118 = zs.length + ys.length + xs.length + 118 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_119 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 119 = zs.length + ys.length + xs.length + 119 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_120 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 120 = zs.length + ys.length + xs.length + 120 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_121 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 121 = zs.length + ys.length + xs.length + 121 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_122 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 122 = zs.length + ys.length + xs.length + 122 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_123 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 123 = zs.length + ys.length + xs.length + 123 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_124 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 124 = zs.length + ys.length + xs.length + 124 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_125 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 125 = zs.length + ys.length + xs.length + 125 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_126 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 126 = zs.length + ys.length + xs.length + 126 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_127 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 127 = zs.length + ys.length + xs.length + 127 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_128 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 128 = zs.length + ys.length + xs.length + 128 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_129 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 129 = zs.length + ys.length + xs.length + 129 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_130 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 130 = zs.length + ys.length + xs.length + 130 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_131 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 131 = zs.length + ys.length + xs.length + 131 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_132 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 132 = zs.length + ys.length + xs.length + 132 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_133 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 133 = zs.length + ys.length + xs.length + 133 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_134 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 134 = zs.length + ys.length + xs.length + 134 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_135 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 135 = zs.length + ys.length + xs.length + 135 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_136 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 136 = zs.length + ys.length + xs.length + 136 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_137 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 137 = zs.length + ys.length + xs.length + 137 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_138 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 138 = zs.length + ys.length + xs.length + 138 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_139 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 139 = zs.length + ys.length + xs.length + 139 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_140 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 140 = zs.length + ys.length + xs.length + 140 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_141 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 141 = zs.length + ys.length + xs.length + 141 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_142 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 142 = zs.length + ys.length + xs.length + 142 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_143 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 143 = zs.length + ys.length + xs.length + 143 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_144 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 144 = zs.length + ys.length + xs.length + 144 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_145 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 145 = zs.length + ys.length + xs.length + 145 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_146 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 146 = zs.length + ys.length + xs.length + 146 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_147 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 147 = zs.length + ys.length + xs.length + 147 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_148 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 148 = zs.length + ys.length + xs.length + 148 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_149 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 149 = zs.length + ys.length + xs.length + 149 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_150 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 150 = zs.length + ys.length + xs.length + 150 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_151 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 151 = zs.length + ys.length + xs.length + 151 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_152 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 152 = zs.length + ys.length + xs.length + 152 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_153 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 153 = zs.length + ys.length + xs.length + 153 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_154 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 154 = zs.length + ys.length + xs.length + 154 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_155 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 155 = zs.length + ys.length + xs.length + 155 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_156 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 156 = zs.length + ys.length + xs.length + 156 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_157 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 157 = zs.length + ys.length + xs.length + 157 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_158 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 158 = zs.length + ys.length + xs.length + 158 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_159 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 159 = zs.length + ys.length + xs.length + 159 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_160 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 160 = zs.length + ys.length + xs.length + 160 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_161 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 161 = zs.length + ys.length + xs.length + 161 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_162 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 162 = zs.length + ys.length + xs.length + 162 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_163 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 163 = zs.length + ys.length + xs.length + 163 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_164 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 164 = zs.length + ys.length + xs.length + 164 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_165 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 165 = zs.length + ys.length + xs.length + 165 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_166 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 166 = zs.length + ys.length + xs.length + 166 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_167 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 167 = zs.length + ys.length + xs.length + 167 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_168 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 168 = zs.length + ys.length + xs.length + 168 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_169 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 169 = zs.length + ys.length + xs.length + 169 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_170 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 170 = zs.length + ys.length + xs.length + 170 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_171 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 171 = zs.length + ys.length + xs.length + 171 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_172 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 172 = zs.length + ys.length + xs.length + 172 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_173 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 173 = zs.length + ys.length + xs.length + 173 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_174 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 174 = zs.length + ys.length + xs.length + 174 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_175 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 175 = zs.length + ys.length + xs.length + 175 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_176 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 176 = zs.length + ys.length + xs.length + 176 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_177 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 177 = zs.length + ys.length + xs.length + 177 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_178 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 178 = zs.length + ys.length + xs.length + 178 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_179 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 179 = zs.length + ys.length + xs.length + 179 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_180 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 180 = zs.length + ys.length + xs.length + 180 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_181 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 181 = zs.length + ys.length + xs.length + 181 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_182 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 182 = zs.length + ys.length + xs.length + 182 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_183 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 183 = zs.length + ys.length + xs.length + 183 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_184 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 184 = zs.length + ys.length + xs.length + 184 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_185 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 185 = zs.length + ys.length + xs.length + 185 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_186 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 186 = zs.length + ys.length + xs.length + 186 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_187 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 187 = zs.length + ys.length + xs.length + 187 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_188 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 188 = zs.length + ys.length + xs.length + 188 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_189 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 189 = zs.length + ys.length + xs.length + 189 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_190 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 190 = zs.length + ys.length + xs.length + 190 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_191 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 191 = zs.length + ys.length + xs.length + 191 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_192 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 192 = zs.length + ys.length + xs.length + 192 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_193 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 193 = zs.length + ys.length + xs.length + 193 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_194 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 194 = zs.length + ys.length + xs.length + 194 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_195 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 195 = zs.length + ys.length + xs.length + 195 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_196 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 196 = zs.length + ys.length + xs.length + 196 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_197 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 197 = zs.length + ys.length + xs.length + 197 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_198 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 198 = zs.length + ys.length + xs.length + 198 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_199 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 199 = zs.length + ys.length + xs.length + 199 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_200 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 200 = zs.length + ys.length + xs.length + 200 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_201 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 201 = zs.length + ys.length + xs.length + 201 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_202 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 202 = zs.length + ys.length + xs.length + 202 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_203 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 203 = zs.length + ys.length + xs.length + 203 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_204 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 204 = zs.length + ys.length + xs.length + 204 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_205 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 205 = zs.length + ys.length + xs.length + 205 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_206 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 206 = zs.length + ys.length + xs.length + 206 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_207 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 207 = zs.length + ys.length + xs.length + 207 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_208 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 208 = zs.length + ys.length + xs.length + 208 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_209 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 209 = zs.length + ys.length + xs.length + 209 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_210 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 210 = zs.length + ys.length + xs.length + 210 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_211 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 211 = zs.length + ys.length + xs.length + 211 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_212 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 212 = zs.length + ys.length + xs.length + 212 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_213 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 213 = zs.length + ys.length + xs.length + 213 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_214 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 214 = zs.length + ys.length + xs.length + 214 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_215 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 215 = zs.length + ys.length + xs.length + 215 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_216 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 216 = zs.length + ys.length + xs.length + 216 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_217 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 217 = zs.length + ys.length + xs.length + 217 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_218 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 218 = zs.length + ys.length + xs.length + 218 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_219 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 219 = zs.length + ys.length + xs.length + 219 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_220 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 220 = zs.length + ys.length + xs.length + 220 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_221 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 221 = zs.length + ys.length + xs.length + 221 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_222 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 222 = zs.length + ys.length + xs.length + 222 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_223 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 223 = zs.length + ys.length + xs.length + 223 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_224 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 224 = zs.length + ys.length + xs.length + 224 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_225 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 225 = zs.length + ys.length + xs.length + 225 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_226 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 226 = zs.length + ys.length + xs.length + 226 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_227 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 227 = zs.length + ys.length + xs.length + 227 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_228 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 228 = zs.length + ys.length + xs.length + 228 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_229 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 229 = zs.length + ys.length + xs.length + 229 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_230 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 230 = zs.length + ys.length + xs.length + 230 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_231 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 231 = zs.length + ys.length + xs.length + 231 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_232 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 232 = zs.length + ys.length + xs.length + 232 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_233 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 233 = zs.length + ys.length + xs.length + 233 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_234 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 234 = zs.length + ys.length + xs.length + 234 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_235 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 235 = zs.length + ys.length + xs.length + 235 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_236 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 236 = zs.length + ys.length + xs.length + 236 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_237 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 237 = zs.length + ys.length + xs.length + 237 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_238 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 238 = zs.length + ys.length + xs.length + 238 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_239 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 239 = zs.length + ys.length + xs.length + 239 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_240 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 240 = zs.length + ys.length + xs.length + 240 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_241 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 241 = zs.length + ys.length + xs.length + 241 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_242 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 242 = zs.length + ys.length + xs.length + 242 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_243 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 243 = zs.length + ys.length + xs.length + 243 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_244 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 244 = zs.length + ys.length + xs.length + 244 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_245 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 245 = zs.length + ys.length + xs.length + 245 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_246 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 246 = zs.length + ys.length + xs.length + 246 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_247 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 247 = zs.length + ys.length + xs.length + 247 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_248 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 248 = zs.length + ys.length + xs.length + 248 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_249 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 249 = zs.length + ys.length + xs.length + 249 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_250 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 250 = zs.length + ys.length + xs.length + 250 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_251 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 251 = zs.length + ys.length + xs.length + 251 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_252 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 252 = zs.length + ys.length + xs.length + 252 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_253 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 253 = zs.length + ys.length + xs.length + 253 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_254 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 254 = zs.length + ys.length + xs.length + 254 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_255 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 255 = zs.length + ys.length + xs.length + 255 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_256 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 256 = zs.length + ys.length + xs.length + 256 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_257 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 257 = zs.length + ys.length + xs.length + 257 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_258 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 258 = zs.length + ys.length + xs.length + 258 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_259 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 259 = zs.length + ys.length + xs.length + 259 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_260 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 260 = zs.length + ys.length + xs.length + 260 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_261 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 261 = zs.length + ys.length + xs.length + 261 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_262 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 262 = zs.length + ys.length + xs.length + 262 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_263 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 263 = zs.length + ys.length + xs.length + 263 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_264 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 264 = zs.length + ys.length + xs.length + 264 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_265 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 265 = zs.length + ys.length + xs.length + 265 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_266 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 266 = zs.length + ys.length + xs.length + 266 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_267 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 267 = zs.length + ys.length + xs.length + 267 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_268 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 268 = zs.length + ys.length + xs.length + 268 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_269 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 269 = zs.length + ys.length + xs.length + 269 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_270 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 270 = zs.length + ys.length + xs.length + 270 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_271 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 271 = zs.length + ys.length + xs.length + 271 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_272 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 272 = zs.length + ys.length + xs.length + 272 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_273 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 273 = zs.length + ys.length + xs.length + 273 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_274 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 274 = zs.length + ys.length + xs.length + 274 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_275 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 275 = zs.length + ys.length + xs.length + 275 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_276 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 276 = zs.length + ys.length + xs.length + 276 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_277 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 277 = zs.length + ys.length + xs.length + 277 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_278 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 278 = zs.length + ys.length + xs.length + 278 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_279 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 279 = zs.length + ys.length + xs.length + 279 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_280 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 280 = zs.length + ys.length + xs.length + 280 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_281 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 281 = zs.length + ys.length + xs.length + 281 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_282 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 282 = zs.length + ys.length + xs.length + 282 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_283 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 283 = zs.length + ys.length + xs.length + 283 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_284 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 284 = zs.length + ys.length + xs.length + 284 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_285 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 285 = zs.length + ys.length + xs.length + 285 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_286 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 286 = zs.length + ys.length + xs.length + 286 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_287 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 287 = zs.length + ys.length + xs.length + 287 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_288 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 288 = zs.length + ys.length + xs.length + 288 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_289 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 289 = zs.length + ys.length + xs.length + 289 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_290 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 290 = zs.length + ys.length + xs.length + 290 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_291 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 291 = zs.length + ys.length + xs.length + 291 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_292 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 292 = zs.length + ys.length + xs.length + 292 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_293 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 293 = zs.length + ys.length + xs.length + 293 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_294 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 294 = zs.length + ys.length + xs.length + 294 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_295 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 295 = zs.length + ys.length + xs.length + 295 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_296 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 296 = zs.length + ys.length + xs.length + 296 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_297 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 297 = zs.length + ys.length + xs.length + 297 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_298 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 298 = zs.length + ys.length + xs.length + 298 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_299 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 299 = zs.length + ys.length + xs.length + 299 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem simp_300 (xs ys zs : List Nat) :
    (xs ++ ys ++ zs).length + 300 = zs.length + ys.length + xs.length + 300 := by
  simp [Nat.add_comm, Nat.add_left_comm]

theorem kernel_1 : (List.range 308).foldl (· + ·) 0 = (307 * 308) / 2 := by decide +kernel

theorem kernel_2 : (List.range 316).foldl (· + ·) 0 = (315 * 316) / 2 := by decide +kernel

theorem kernel_3 : (List.range 324).foldl (· + ·) 0 = (323 * 324) / 2 := by decide +kernel

theorem kernel_4 : (List.range 332).foldl (· + ·) 0 = (331 * 332) / 2 := by decide +kernel

theorem kernel_5 : (List.range 340).foldl (· + ·) 0 = (339 * 340) / 2 := by decide +kernel

theorem kernel_6 : (List.range 348).foldl (· + ·) 0 = (347 * 348) / 2 := by decide +kernel

theorem kernel_7 : (List.range 356).foldl (· + ·) 0 = (355 * 356) / 2 := by decide +kernel

theorem kernel_8 : (List.range 364).foldl (· + ·) 0 = (363 * 364) / 2 := by decide +kernel

theorem kernel_9 : (List.range 372).foldl (· + ·) 0 = (371 * 372) / 2 := by decide +kernel

theorem kernel_10 : (List.range 380).foldl (· + ·) 0 = (379 * 380) / 2 := by decide +kernel

theorem kernel_11 : (List.range 388).foldl (· + ·) 0 = (387 * 388) / 2 := by decide +kernel

theorem kernel_12 : (List.range 396).foldl (· + ·) 0 = (395 * 396) / 2 := by decide +kernel

theorem kernel_13 : (List.range 404).foldl (· + ·) 0 = (403 * 404) / 2 := by decide +kernel

theorem kernel_14 : (List.range 412).foldl (· + ·) 0 = (411 * 412) / 2 := by decide +kernel

theorem kernel_15 : (List.range 420).foldl (· + ·) 0 = (419 * 420) / 2 := by decide +kernel

theorem kernel_16 : (List.range 428).foldl (· + ·) 0 = (427 * 428) / 2 := by decide +kernel

theorem kernel_17 : (List.range 436).foldl (· + ·) 0 = (435 * 436) / 2 := by decide +kernel

theorem kernel_18 : (List.range 444).foldl (· + ·) 0 = (443 * 444) / 2 := by decide +kernel

theorem kernel_19 : (List.range 452).foldl (· + ·) 0 = (451 * 452) / 2 := by decide +kernel

theorem kernel_20 : (List.range 460).foldl (· + ·) 0 = (459 * 460) / 2 := by decide +kernel

theorem kernel_21 : (List.range 468).foldl (· + ·) 0 = (467 * 468) / 2 := by decide +kernel

theorem kernel_22 : (List.range 476).foldl (· + ·) 0 = (475 * 476) / 2 := by decide +kernel

theorem kernel_23 : (List.range 484).foldl (· + ·) 0 = (483 * 484) / 2 := by decide +kernel

theorem kernel_24 : (List.range 492).foldl (· + ·) 0 = (491 * 492) / 2 := by decide +kernel

theorem kernel_25 : (List.range 500).foldl (· + ·) 0 = (499 * 500) / 2 := by decide +kernel

theorem kernel_26 : (List.range 508).foldl (· + ·) 0 = (507 * 508) / 2 := by decide +kernel

theorem kernel_27 : (List.range 516).foldl (· + ·) 0 = (515 * 516) / 2 := by decide +kernel

theorem kernel_28 : (List.range 524).foldl (· + ·) 0 = (523 * 524) / 2 := by decide +kernel

theorem kernel_29 : (List.range 532).foldl (· + ·) 0 = (531 * 532) / 2 := by decide +kernel

theorem kernel_30 : (List.range 540).foldl (· + ·) 0 = (539 * 540) / 2 := by decide +kernel

theorem kernel_31 : (List.range 548).foldl (· + ·) 0 = (547 * 548) / 2 := by decide +kernel

theorem kernel_32 : (List.range 556).foldl (· + ·) 0 = (555 * 556) / 2 := by decide +kernel

theorem kernel_33 : (List.range 564).foldl (· + ·) 0 = (563 * 564) / 2 := by decide +kernel

theorem kernel_34 : (List.range 572).foldl (· + ·) 0 = (571 * 572) / 2 := by decide +kernel

theorem kernel_35 : (List.range 580).foldl (· + ·) 0 = (579 * 580) / 2 := by decide +kernel

theorem kernel_36 : (List.range 588).foldl (· + ·) 0 = (587 * 588) / 2 := by decide +kernel

theorem kernel_37 : (List.range 596).foldl (· + ·) 0 = (595 * 596) / 2 := by decide +kernel

theorem kernel_38 : (List.range 604).foldl (· + ·) 0 = (603 * 604) / 2 := by decide +kernel

theorem kernel_39 : (List.range 612).foldl (· + ·) 0 = (611 * 612) / 2 := by decide +kernel

theorem kernel_40 : (List.range 620).foldl (· + ·) 0 = (619 * 620) / 2 := by decide +kernel

theorem kernel_41 : (List.range 628).foldl (· + ·) 0 = (627 * 628) / 2 := by decide +kernel

theorem kernel_42 : (List.range 636).foldl (· + ·) 0 = (635 * 636) / 2 := by decide +kernel

theorem kernel_43 : (List.range 644).foldl (· + ·) 0 = (643 * 644) / 2 := by decide +kernel

theorem kernel_44 : (List.range 652).foldl (· + ·) 0 = (651 * 652) / 2 := by decide +kernel

theorem kernel_45 : (List.range 660).foldl (· + ·) 0 = (659 * 660) / 2 := by decide +kernel

theorem kernel_46 : (List.range 668).foldl (· + ·) 0 = (667 * 668) / 2 := by decide +kernel

theorem kernel_47 : (List.range 676).foldl (· + ·) 0 = (675 * 676) / 2 := by decide +kernel

theorem kernel_48 : (List.range 684).foldl (· + ·) 0 = (683 * 684) / 2 := by decide +kernel

theorem kernel_49 : (List.range 692).foldl (· + ·) 0 = (691 * 692) / 2 := by decide +kernel

theorem kernel_50 : (List.range 700).foldl (· + ·) 0 = (699 * 700) / 2 := by decide +kernel

theorem kernel_51 : (List.range 708).foldl (· + ·) 0 = (707 * 708) / 2 := by decide +kernel

theorem kernel_52 : (List.range 716).foldl (· + ·) 0 = (715 * 716) / 2 := by decide +kernel

theorem kernel_53 : (List.range 724).foldl (· + ·) 0 = (723 * 724) / 2 := by decide +kernel

theorem kernel_54 : (List.range 732).foldl (· + ·) 0 = (731 * 732) / 2 := by decide +kernel

theorem kernel_55 : (List.range 740).foldl (· + ·) 0 = (739 * 740) / 2 := by decide +kernel

theorem kernel_56 : (List.range 748).foldl (· + ·) 0 = (747 * 748) / 2 := by decide +kernel

theorem kernel_57 : (List.range 756).foldl (· + ·) 0 = (755 * 756) / 2 := by decide +kernel

theorem kernel_58 : (List.range 764).foldl (· + ·) 0 = (763 * 764) / 2 := by decide +kernel

theorem kernel_59 : (List.range 772).foldl (· + ·) 0 = (771 * 772) / 2 := by decide +kernel

theorem kernel_60 : (List.range 780).foldl (· + ·) 0 = (779 * 780) / 2 := by decide +kernel

theorem kernel_61 : (List.range 788).foldl (· + ·) 0 = (787 * 788) / 2 := by decide +kernel

theorem kernel_62 : (List.range 796).foldl (· + ·) 0 = (795 * 796) / 2 := by decide +kernel

theorem kernel_63 : (List.range 804).foldl (· + ·) 0 = (803 * 804) / 2 := by decide +kernel

theorem kernel_64 : (List.range 812).foldl (· + ·) 0 = (811 * 812) / 2 := by decide +kernel

theorem kernel_65 : (List.range 820).foldl (· + ·) 0 = (819 * 820) / 2 := by decide +kernel

theorem kernel_66 : (List.range 828).foldl (· + ·) 0 = (827 * 828) / 2 := by decide +kernel

theorem kernel_67 : (List.range 836).foldl (· + ·) 0 = (835 * 836) / 2 := by decide +kernel

theorem kernel_68 : (List.range 844).foldl (· + ·) 0 = (843 * 844) / 2 := by decide +kernel

theorem kernel_69 : (List.range 852).foldl (· + ·) 0 = (851 * 852) / 2 := by decide +kernel

theorem kernel_70 : (List.range 860).foldl (· + ·) 0 = (859 * 860) / 2 := by decide +kernel

theorem kernel_71 : (List.range 868).foldl (· + ·) 0 = (867 * 868) / 2 := by decide +kernel

theorem kernel_72 : (List.range 876).foldl (· + ·) 0 = (875 * 876) / 2 := by decide +kernel

theorem kernel_73 : (List.range 884).foldl (· + ·) 0 = (883 * 884) / 2 := by decide +kernel

theorem kernel_74 : (List.range 892).foldl (· + ·) 0 = (891 * 892) / 2 := by decide +kernel

theorem kernel_75 : (List.range 900).foldl (· + ·) 0 = (899 * 900) / 2 := by decide +kernel

theorem kernel_76 : (List.range 908).foldl (· + ·) 0 = (907 * 908) / 2 := by decide +kernel

theorem kernel_77 : (List.range 916).foldl (· + ·) 0 = (915 * 916) / 2 := by decide +kernel

theorem kernel_78 : (List.range 924).foldl (· + ·) 0 = (923 * 924) / 2 := by decide +kernel

theorem kernel_79 : (List.range 932).foldl (· + ·) 0 = (931 * 932) / 2 := by decide +kernel

theorem kernel_80 : (List.range 940).foldl (· + ·) 0 = (939 * 940) / 2 := by decide +kernel

theorem kernel_81 : (List.range 948).foldl (· + ·) 0 = (947 * 948) / 2 := by decide +kernel

theorem kernel_82 : (List.range 956).foldl (· + ·) 0 = (955 * 956) / 2 := by decide +kernel

theorem kernel_83 : (List.range 964).foldl (· + ·) 0 = (963 * 964) / 2 := by decide +kernel

theorem kernel_84 : (List.range 972).foldl (· + ·) 0 = (971 * 972) / 2 := by decide +kernel

theorem kernel_85 : (List.range 980).foldl (· + ·) 0 = (979 * 980) / 2 := by decide +kernel

theorem kernel_86 : (List.range 988).foldl (· + ·) 0 = (987 * 988) / 2 := by decide +kernel

theorem kernel_87 : (List.range 996).foldl (· + ·) 0 = (995 * 996) / 2 := by decide +kernel

theorem kernel_88 : (List.range 1004).foldl (· + ·) 0 = (1003 * 1004) / 2 := by decide +kernel

theorem kernel_89 : (List.range 1012).foldl (· + ·) 0 = (1011 * 1012) / 2 := by decide +kernel

theorem kernel_90 : (List.range 1020).foldl (· + ·) 0 = (1019 * 1020) / 2 := by decide +kernel

theorem kernel_91 : (List.range 1028).foldl (· + ·) 0 = (1027 * 1028) / 2 := by decide +kernel

theorem kernel_92 : (List.range 1036).foldl (· + ·) 0 = (1035 * 1036) / 2 := by decide +kernel

theorem kernel_93 : (List.range 1044).foldl (· + ·) 0 = (1043 * 1044) / 2 := by decide +kernel

theorem kernel_94 : (List.range 1052).foldl (· + ·) 0 = (1051 * 1052) / 2 := by decide +kernel

theorem kernel_95 : (List.range 1060).foldl (· + ·) 0 = (1059 * 1060) / 2 := by decide +kernel

theorem kernel_96 : (List.range 1068).foldl (· + ·) 0 = (1067 * 1068) / 2 := by decide +kernel

theorem kernel_97 : (List.range 1076).foldl (· + ·) 0 = (1075 * 1076) / 2 := by decide +kernel

theorem kernel_98 : (List.range 1084).foldl (· + ·) 0 = (1083 * 1084) / 2 := by decide +kernel

theorem kernel_99 : (List.range 1092).foldl (· + ·) 0 = (1091 * 1092) / 2 := by decide +kernel

theorem kernel_100 : (List.range 1100).foldl (· + ·) 0 = (1099 * 1100) / 2 := by decide +kernel

theorem kernel_101 : (List.range 1108).foldl (· + ·) 0 = (1107 * 1108) / 2 := by decide +kernel

theorem kernel_102 : (List.range 1116).foldl (· + ·) 0 = (1115 * 1116) / 2 := by decide +kernel

theorem kernel_103 : (List.range 1124).foldl (· + ·) 0 = (1123 * 1124) / 2 := by decide +kernel

theorem kernel_104 : (List.range 1132).foldl (· + ·) 0 = (1131 * 1132) / 2 := by decide +kernel

theorem kernel_105 : (List.range 1140).foldl (· + ·) 0 = (1139 * 1140) / 2 := by decide +kernel

theorem kernel_106 : (List.range 1148).foldl (· + ·) 0 = (1147 * 1148) / 2 := by decide +kernel

theorem kernel_107 : (List.range 1156).foldl (· + ·) 0 = (1155 * 1156) / 2 := by decide +kernel

theorem kernel_108 : (List.range 1164).foldl (· + ·) 0 = (1163 * 1164) / 2 := by decide +kernel

theorem kernel_109 : (List.range 1172).foldl (· + ·) 0 = (1171 * 1172) / 2 := by decide +kernel

theorem kernel_110 : (List.range 1180).foldl (· + ·) 0 = (1179 * 1180) / 2 := by decide +kernel

theorem kernel_111 : (List.range 1188).foldl (· + ·) 0 = (1187 * 1188) / 2 := by decide +kernel

theorem kernel_112 : (List.range 1196).foldl (· + ·) 0 = (1195 * 1196) / 2 := by decide +kernel

theorem kernel_113 : (List.range 1204).foldl (· + ·) 0 = (1203 * 1204) / 2 := by decide +kernel

theorem kernel_114 : (List.range 1212).foldl (· + ·) 0 = (1211 * 1212) / 2 := by decide +kernel

theorem kernel_115 : (List.range 1220).foldl (· + ·) 0 = (1219 * 1220) / 2 := by decide +kernel

theorem kernel_116 : (List.range 1228).foldl (· + ·) 0 = (1227 * 1228) / 2 := by decide +kernel

theorem kernel_117 : (List.range 1236).foldl (· + ·) 0 = (1235 * 1236) / 2 := by decide +kernel

theorem kernel_118 : (List.range 1244).foldl (· + ·) 0 = (1243 * 1244) / 2 := by decide +kernel

theorem kernel_119 : (List.range 1252).foldl (· + ·) 0 = (1251 * 1252) / 2 := by decide +kernel

theorem kernel_120 : (List.range 1260).foldl (· + ·) 0 = (1259 * 1260) / 2 := by decide +kernel

theorem decide_1 : ∀ a : Fin 7, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_2 : ∀ a : Fin 8, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_3 : ∀ a : Fin 9, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_4 : ∀ a : Fin 10, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_5 : ∀ a : Fin 6, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_6 : ∀ a : Fin 7, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_7 : ∀ a : Fin 8, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_8 : ∀ a : Fin 9, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_9 : ∀ a : Fin 10, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_10 : ∀ a : Fin 6, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_11 : ∀ a : Fin 7, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_12 : ∀ a : Fin 8, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_13 : ∀ a : Fin 9, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_14 : ∀ a : Fin 10, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_15 : ∀ a : Fin 6, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_16 : ∀ a : Fin 7, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_17 : ∀ a : Fin 8, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_18 : ∀ a : Fin 9, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_19 : ∀ a : Fin 10, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_20 : ∀ a : Fin 6, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_21 : ∀ a : Fin 7, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_22 : ∀ a : Fin 8, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_23 : ∀ a : Fin 9, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_24 : ∀ a : Fin 10, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_25 : ∀ a : Fin 6, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_26 : ∀ a : Fin 7, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_27 : ∀ a : Fin 8, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_28 : ∀ a : Fin 9, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_29 : ∀ a : Fin 10, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_30 : ∀ a : Fin 6, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_31 : ∀ a : Fin 7, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_32 : ∀ a : Fin 8, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_33 : ∀ a : Fin 9, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_34 : ∀ a : Fin 10, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_35 : ∀ a : Fin 6, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_36 : ∀ a : Fin 7, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_37 : ∀ a : Fin 8, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_38 : ∀ a : Fin 9, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_39 : ∀ a : Fin 10, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_40 : ∀ a : Fin 6, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_41 : ∀ a : Fin 7, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_42 : ∀ a : Fin 8, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_43 : ∀ a : Fin 9, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_44 : ∀ a : Fin 10, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_45 : ∀ a : Fin 6, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_46 : ∀ a : Fin 7, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_47 : ∀ a : Fin 8, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_48 : ∀ a : Fin 9, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_49 : ∀ a : Fin 10, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_50 : ∀ a : Fin 6, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_51 : ∀ a : Fin 7, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_52 : ∀ a : Fin 8, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_53 : ∀ a : Fin 9, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_54 : ∀ a : Fin 10, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_55 : ∀ a : Fin 6, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_56 : ∀ a : Fin 7, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_57 : ∀ a : Fin 8, ∀ b : Fin 7, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_58 : ∀ a : Fin 9, ∀ b : Fin 8, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_59 : ∀ a : Fin 10, ∀ b : Fin 9, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide

theorem decide_60 : ∀ a : Fin 6, ∀ b : Fin 6, (a.val + b.val) * 2 = 2 * (b.val + a.val) := by decide
