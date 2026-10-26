------------------------------------------------------------------------
-- Presentations of groups
--
-- Five-wire derivations by reflection
--
-- A derivation of Five/D as a list of steps checked by running it, as
-- Clifford+CS.Engine does over generators: `rw k e` replaces the
-- left-hand side of an equation e found at position k by its right-hand
-- side (`rw⁻` the other way round), and `re k n ys` replaces the n
-- letters at k by ys when the two spell the same generators (a
-- re-bracketing, `by-assoc`).  The line is a list of macro letters
-- (Five.Letters), so that a step costs a comparison of a few letters;
-- only a re-bracketing compares generators (sameG).  The line is a
-- zipper, so that a step at position k costs its distance from the step
-- before rather than k.  `derive l r ss Eq.refl` checks the whole run
-- in one evaluation, its result compared with r inside it, and gives
-- ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ.  Written by
-- `scratchpad/five/reflect5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Reflect where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; T)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; take ; drop ; map)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; pred ; _∸_ ; _≡ᵇ_ ; _<ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Word.Base using (_•_)

open import Presentation.Tactic.AssociativitySolver using (module Assoc)

open import Examples.Groups.Clifford+CS.Syntactics hiding (_⊢_≈_)
open import Examples.Groups.Clifford+CS.Five.Rules using (_XVRel,_===_)
open import Examples.Groups.Clifford+CS.Five.Chain hiding (Step ; step′ ; at ; Chain ; done ; _▸_ ; run)

open Assoc (_XVRel,_===_ 5) using (to-list)

------------------------------------------------------------------------
-- Codes

private
  ix : {A : Set} → A → List A → ℕ → A
  ix d []       _       = d
  ix d (x ∷ xs) zero    = x
  ix d (x ∷ xs) (suc n) = ix d xs n

codeM : Mac → ℕ
codeM (ι)           = 0
codeM (ι⁻)          = 1
codeM (ι1)          = 2
codeM (ι1⁻)         = 3
codeM (ι2)          = 4
codeM (ι2⁻)         = 5
codeM (ι3)          = 6
codeM (ι3⁻)         = 7
codeM (ι4)          = 8
codeM (ι4⁻)         = 9
codeM (S0)          = 10
codeM (S0⁻)         = 11
codeM (K0)          = 12
codeM (K0⁻)         = 13
codeM (X0)          = 14
codeM (Z0)          = 15
codeM (S1)          = 16
codeM (S1⁻)         = 17
codeM (K1)          = 18
codeM (K1⁻)         = 19
codeM (X1)          = 20
codeM (Z1)          = 21
codeM (S2)          = 22
codeM (S2⁻)         = 23
codeM (K2)          = 24
codeM (K2⁻)         = 25
codeM (X2)          = 26
codeM (Z2)          = 27
codeM (S3)          = 28
codeM (S3⁻)         = 29
codeM (K3)          = 30
codeM (K3⁻)         = 31
codeM (X3)          = 32
codeM (Z3)          = 33
codeM (S4)          = 34
codeM (S4⁻)         = 35
codeM (K4)          = 36
codeM (K4⁻)         = 37
codeM (X4)          = 38
codeM (Z4)          = 39
codeM (CS01)        = 40
codeM (CS01⁻)       = 41
codeM (CZ01)        = 42
codeM (Sw01)        = 43
codeM (CX01)        = 44
codeM (CK01)        = 45
codeM (CK01⁻)       = 46
codeM (CS02)        = 47
codeM (CS02⁻)       = 48
codeM (CZ02)        = 49
codeM (Sw02)        = 50
codeM (CX02)        = 51
codeM (CK02)        = 52
codeM (CK02⁻)       = 53
codeM (CS03)        = 54
codeM (CS03⁻)       = 55
codeM (CZ03)        = 56
codeM (Sw03)        = 57
codeM (CX03)        = 58
codeM (CK03)        = 59
codeM (CK03⁻)       = 60
codeM (CS04)        = 61
codeM (CS04⁻)       = 62
codeM (CZ04)        = 63
codeM (Sw04)        = 64
codeM (CX04)        = 65
codeM (CK04)        = 66
codeM (CK04⁻)       = 67
codeM (CX10)        = 68
codeM (CK10)        = 69
codeM (CK10⁻)       = 70
codeM (CS12)        = 71
codeM (CS12⁻)       = 72
codeM (CZ12)        = 73
codeM (Sw12)        = 74
codeM (CX12)        = 75
codeM (CK12)        = 76
codeM (CK12⁻)       = 77
codeM (CS13)        = 78
codeM (CS13⁻)       = 79
codeM (CZ13)        = 80
codeM (Sw13)        = 81
codeM (CX13)        = 82
codeM (CK13)        = 83
codeM (CK13⁻)       = 84
codeM (CS14)        = 85
codeM (CS14⁻)       = 86
codeM (CZ14)        = 87
codeM (Sw14)        = 88
codeM (CX14)        = 89
codeM (CK14)        = 90
codeM (CK14⁻)       = 91
codeM (CX20)        = 92
codeM (CK20)        = 93
codeM (CK20⁻)       = 94
codeM (CX21)        = 95
codeM (CK21)        = 96
codeM (CK21⁻)       = 97
codeM (CS23)        = 98
codeM (CS23⁻)       = 99
codeM (CZ23)        = 100
codeM (Sw23)        = 101
codeM (CX23)        = 102
codeM (CK23)        = 103
codeM (CK23⁻)       = 104
codeM (CS24)        = 105
codeM (CS24⁻)       = 106
codeM (CZ24)        = 107
codeM (Sw24)        = 108
codeM (CX24)        = 109
codeM (CK24)        = 110
codeM (CK24⁻)       = 111
codeM (CX30)        = 112
codeM (CK30)        = 113
codeM (CK30⁻)       = 114
codeM (CX31)        = 115
codeM (CK31)        = 116
codeM (CK31⁻)       = 117
codeM (CX32)        = 118
codeM (CK32)        = 119
codeM (CK32⁻)       = 120
codeM (CS34)        = 121
codeM (CS34⁻)       = 122
codeM (CZ34)        = 123
codeM (Sw34)        = 124
codeM (CX34)        = 125
codeM (CK34)        = 126
codeM (CK34⁻)       = 127
codeM (CX40)        = 128
codeM (CK40)        = 129
codeM (CK40⁻)       = 130
codeM (CX41)        = 131
codeM (CK41)        = 132
codeM (CK41⁻)       = 133
codeM (CX42)        = 134
codeM (CK42)        = 135
codeM (CK42⁻)       = 136
codeM (CX43)        = 137
codeM (CK43)        = 138
codeM (CK43⁻)       = 139
codeM (CCZ012)      = 140
codeM (Toff012)     = 141
codeM (Toff102)     = 142
codeM (Toff201)     = 143
codeM (CCZ013)      = 144
codeM (Toff013)     = 145
codeM (Toff103)     = 146
codeM (Toff301)     = 147
codeM (CCZ014)      = 148
codeM (Toff014)     = 149
codeM (Toff104)     = 150
codeM (Toff401)     = 151
codeM (CCZ023)      = 152
codeM (Toff023)     = 153
codeM (Toff203)     = 154
codeM (Toff302)     = 155
codeM (CCZ024)      = 156
codeM (Toff024)     = 157
codeM (Toff204)     = 158
codeM (Toff402)     = 159
codeM (CCZ034)      = 160
codeM (Toff034)     = 161
codeM (Toff304)     = 162
codeM (Toff403)     = 163
codeM (CCZ123)      = 164
codeM (Toff123)     = 165
codeM (Toff213)     = 166
codeM (Toff312)     = 167
codeM (CCZ124)      = 168
codeM (Toff124)     = 169
codeM (Toff214)     = 170
codeM (Toff412)     = 171
codeM (CCZ134)      = 172
codeM (Toff134)     = 173
codeM (Toff314)     = 174
codeM (Toff413)     = 175
codeM (CCZ234)      = 176
codeM (Toff234)     = 177
codeM (Toff324)     = 178
codeM (Toff423)     = 179
codeM (Bx0-12)      = 180
codeM (Bx1-03)      = 181
codeM (Bx0-123)     = 182
codeM (Bx0-14)      = 183
codeM (Bx1-034)     = 184
codeM (Bx0-1234)    = 185
codeM (Bx0-13)      = 186
codeM (Bx1-043)     = 187
codeM (Bx0-1243)    = 188
codeM (Bx1-024)     = 189
codeM (Bx0-1324)    = 190
codeM (Bx1-04)      = 191
codeM (Bx0-134)     = 192
codeM (Bx1-042)     = 193
codeM (Bx0-1342)    = 194
codeM (Bx1-023)     = 195
codeM (Bx0-1423)    = 196
codeM (Bx1-032)     = 197
codeM (Bx0-1432)    = 198
codeM (Bx0-21)      = 199
codeM (Bx2-03)      = 200
codeM (Bx0-213)     = 201
codeM (Bx0-24)      = 202
codeM (Bx2-034)     = 203
codeM (Bx0-2134)    = 204
codeM (Bx2-04)      = 205
codeM (Bx0-214)     = 206
codeM (Bx0-23)      = 207
codeM (Bx2-043)     = 208
codeM (Bx0-2143)    = 209
codeM (Bx2-01)      = 210
codeM (Bx0-231)     = 211
codeM (Bx2-014)     = 212
codeM (Bx0-2314)    = 213
codeM (Bx0-234)     = 214
codeM (Bx2-041)     = 215
codeM (Bx0-2341)    = 216
codeM (Bx0-241)     = 217
codeM (Bx2-013)     = 218
codeM (Bx0-2413)    = 219
codeM (Bx0-243)     = 220
codeM (Bx2-031)     = 221
codeM (Bx0-2431)    = 222
codeM (Bx0-31)      = 223
codeM (Bx3-02)      = 224
codeM (Bx0-312)     = 225
codeM (Bx0-34)      = 226
codeM (Bx3-024)     = 227
codeM (Bx0-3124)    = 228
codeM (Bx3-04)      = 229
codeM (Bx0-314)     = 230
codeM (Bx0-32)      = 231
codeM (Bx3-042)     = 232
codeM (Bx0-3142)    = 233
codeM (Bx3-01)      = 234
codeM (Bx0-321)     = 235
codeM (Bx3-014)     = 236
codeM (Bx0-3214)    = 237
codeM (Bx0-324)     = 238
codeM (Bx3-041)     = 239
codeM (Bx0-3241)    = 240
codeM (Bx0-341)     = 241
codeM (Bx3-012)     = 242
codeM (Bx0-3412)    = 243
codeM (Bx0-342)     = 244
codeM (Bx3-021)     = 245
codeM (Bx0-3421)    = 246
codeM (Bx0-41)      = 247
codeM (Bx4-02)      = 248
codeM (Bx0-412)     = 249
codeM (Bx0-43)      = 250
codeM (Bx4-023)     = 251
codeM (Bx0-4123)    = 252
codeM (Bx4-03)      = 253
codeM (Bx0-413)     = 254
codeM (Bx0-42)      = 255
codeM (Bx4-032)     = 256
codeM (Bx0-4132)    = 257
codeM (Bx4-01)      = 258
codeM (Bx0-421)     = 259
codeM (Bx4-013)     = 260
codeM (Bx0-4213)    = 261
codeM (Bx0-423)     = 262
codeM (Bx4-031)     = 263
codeM (Bx0-4231)    = 264
codeM (Bx0-431)     = 265
codeM (Bx4-012)     = 266
codeM (Bx0-4312)    = 267
codeM (Bx4-021)     = 268
codeM (Bx0-4321)    = 269
codeM (Bx1-0234)    = 270
codeM (Bx1-0423)    = 271
codeM (Bx1-20)      = 272
codeM (Bx2-14)      = 273
codeM (Bx1-204)     = 274
codeM (Bx2-10)      = 275
codeM (Bx1-230)     = 276
codeM (Bx1-234)     = 277
codeM (Bx1-240)     = 278
codeM (Bx2-130)     = 279
codeM (Bx1-2430)    = 280
codeM (Bx3-12)      = 281
codeM (Bx1-302)     = 282
codeM (Bx3-14)      = 283
codeM (Bx1-304)     = 284
codeM (Bx3-10)      = 285
codeM (Bx1-320)     = 286
codeM (Bx1-324)     = 287
codeM (Bx1-340)     = 288
codeM (Bx1-342)     = 289
codeM (Bx4-12)      = 290
codeM (Bx1-402)     = 291
codeM (Bx4-13)      = 292
codeM (Bx1-403)     = 293
codeM (Bx4-10)      = 294
codeM (Bx1-420)     = 295
codeM (Bx1-43)      = 296
codeM (Bx4-103)     = 297
codeM (Bx1-4203)    = 298
codeM (Bx1-423)     = 299
codeM (Bx1-430)     = 300
codeM (Bx2-0134)    = 301
codeM (Bx2-0143)    = 302
codeM (Bx2-0314)    = 303
codeM (Bx2-0341)    = 304
codeM (Bx2-0413)    = 305
codeM (Bx2-0431)    = 306
codeM (Bx2-1034)    = 307
codeM (Bx2-1304)    = 308
codeM (Bx2-1340)    = 309
codeM (Bx2-1430)    = 310
codeM (Bx2-30)      = 311
codeM (Bx3-21)      = 312
codeM (Bx2-301)     = 313
codeM (Bx2-34)      = 314
codeM (Bx3-214)     = 315
codeM (Bx2-3014)    = 316
codeM (Bx3-24)      = 317
codeM (Bx2-304)     = 318
codeM (Bx2-31)      = 319
codeM (Bx3-241)     = 320
codeM (Bx2-3041)    = 321
codeM (Bx3-20)      = 322
codeM (Bx2-310)     = 323
codeM (Bx3-204)     = 324
codeM (Bx2-3104)    = 325
codeM (Bx2-314)     = 326
codeM (Bx3-240)     = 327
codeM (Bx2-3140)    = 328
codeM (Bx2-340)     = 329
codeM (Bx3-201)     = 330
codeM (Bx2-3401)    = 331
codeM (Bx2-341)     = 332
codeM (Bx3-210)     = 333
codeM (Bx2-3410)    = 334
codeM (Bx2-40)      = 335
codeM (Bx4-21)      = 336
codeM (Bx2-401)     = 337
codeM (Bx2-43)      = 338
codeM (Bx4-213)     = 339
codeM (Bx2-4013)    = 340
codeM (Bx4-23)      = 341
codeM (Bx2-403)     = 342
codeM (Bx2-41)      = 343
codeM (Bx4-231)     = 344
codeM (Bx2-4031)    = 345
codeM (Bx4-20)      = 346
codeM (Bx2-410)     = 347
codeM (Bx4-203)     = 348
codeM (Bx2-4103)    = 349
codeM (Bx4-230)     = 350
codeM (Bx2-4130)    = 351
codeM (Bx2-430)     = 352
codeM (Bx4-201)     = 353
codeM (Bx2-4301)    = 354
codeM (Bx2-431)     = 355
codeM (Bx3-0124)    = 356
codeM (Bx3-0142)    = 357
codeM (Bx3-0214)    = 358
codeM (Bx3-0241)    = 359
codeM (Bx3-0412)    = 360
codeM (Bx3-0421)    = 361
codeM (Bx3-1024)    = 362
codeM (Bx3-1042)    = 363
codeM (Bx3-1204)    = 364
codeM (Bx3-1240)    = 365
codeM (Bx3-1402)    = 366
codeM (Bx3-1420)    = 367
codeM (Bx3-2014)    = 368
codeM (Bx3-2041)    = 369
codeM (Bx3-2104)    = 370
codeM (Bx3-2140)    = 371
codeM (Bx3-2401)    = 372
codeM (Bx3-2410)    = 373
codeM (Bx3-40)      = 374
codeM (Bx3-42)      = 375
codeM (Bx4-312)     = 376
codeM (Bx3-4012)    = 377
codeM (Bx4-32)      = 378
codeM (Bx3-402)     = 379
codeM (Bx3-41)      = 380
codeM (Bx4-321)     = 381
codeM (Bx3-4021)    = 382
codeM (Bx4-30)      = 383
codeM (Bx3-410)     = 384
codeM (Bx4-302)     = 385
codeM (Bx3-4102)    = 386
codeM (Bx3-412)     = 387
codeM (Bx4-320)     = 388
codeM (Bx3-4120)    = 389
codeM (Bx3-420)     = 390
codeM (Bx4-301)     = 391
codeM (Bx3-4201)    = 392
codeM (Bx4-31)      = 393
codeM (Bx3-421)     = 394
codeM (Bx4-310)     = 395
codeM (Bx3-4210)    = 396
codeM (Bx4-0123)    = 397
codeM (Bx4-0213)    = 398
codeM (Bx4-0231)    = 399
codeM (Bx4-0312)    = 400
codeM (Bx4-0321)    = 401
codeM (Bx4-1023)    = 402
codeM (Bx4-1203)    = 403
codeM (Bx4-1230)    = 404
codeM (Bx4-1302)    = 405
codeM (Bx4-1320)    = 406
codeM (Bx4-2031)    = 407
codeM (Bx4-2103)    = 408
codeM (Bx4-2130)    = 409
codeM (Bx4-2301)    = 410
codeM (Bx4-2310)    = 411
codeM (Bx4-3012)    = 412
codeM (Bx4-3021)    = 413
codeM (Bx4-3102)    = 414
codeM (Bx4-3120)    = 415
codeM (Bx4-3210)    = 416
codeM (Bx⁻2-03)     = 417
codeM (Bx⁻0-213)    = 418
codeM (Bx⁻2-0413)   = 419
codeM (Sb0-1-2-3)   = 420
codeM (Sb0-1-3-2)   = 421
codeM (Sb⁻0-1-3-2)  = 422
codeM (Sb0-1-42-3)  = 423
codeM (Sb⁻0-1-2-3)  = 424
codeM (Sb0-1-43-2)  = 425
codeM (Sb0-2-1-3)   = 426
codeM (Sb⁻0-2-1-3)  = 427
codeM (Sb0-2-43-1)  = 428
codeM (Sb0-3-1-2)   = 429
codeM (Sb⁻0-3-1-2)  = 430
codeM (Sb0-3-42-1)  = 431
codeM (Sb0-4-1-2)   = 432
codeM (Sb0-4-2-1)   = 433
codeM (Sb0-4-3-1)   = 434
codeM (Sb⁻0-4-3-1)  = 435
codeM (Sb0-4-21-3)  = 436
codeM (Sb⁻0-4-2-1)  = 437
codeM (Sb0-4-31-2)  = 438
codeM (Sb⁻0-4-1-2)  = 439
codeM (Sb0-4-32-1)  = 440
codeM (Sb1-0-3-2)   = 441
codeM (Sb⁻1-0-3-2)  = 442
codeM (Sb1-0-42-3)  = 443
codeM (Sb1-2-0-3)   = 444
codeM (Sb⁻1-2-0-3)  = 445
codeM (Sb1-2-43-0)  = 446
codeM (Sb1-4-3-0)   = 447
codeM (Sb⁻1-4-3-0)  = 448
codeM (Sb1-4-20-3)  = 449
codeM (Sb2-0-3-1)   = 450
codeM (Sb⁻2-0-3-1)  = 451
codeM (Sb2-0-41-3)  = 452
codeM (Sb2-1-0-3)   = 453
codeM (Sb⁻2-1-0-3)  = 454
codeM (Sb2-1-43-0)  = 455
codeM (Sb2-4-3-1)   = 456
codeM (Sb⁻2-4-3-1)  = 457
codeM (Sb2-4-01-3)  = 458
codeM (Sb2-4-3-0)   = 459
codeM (Sb⁻2-4-3-0)  = 460
codeM (Sb2-4-10-3)  = 461
codeM (Sb3-0-4-2)   = 462
codeM (Sb⁻3-0-4-2)  = 463
codeM (Sb3-0-12-4)  = 464
codeM (Sb3-0-2-1)   = 465
codeM (Sb3-0-4-1)   = 466
codeM (Sb⁻3-0-4-1)  = 467
codeM (Sb3-0-21-4)  = 468
codeM (Sb⁻3-0-2-1)  = 469
codeM (Sb3-0-41-2)  = 470
codeM (Sb3-1-0-2)   = 471
codeM (Sb3-1-4-2)   = 472
codeM (Sb⁻3-1-4-2)  = 473
codeM (Sb3-1-02-4)  = 474
codeM (Sb⁻3-1-0-2)  = 475
codeM (Sb3-1-42-0)  = 476
codeM (Sb3-4-2-1)   = 477
codeM (Sb⁻3-4-2-1)  = 478
codeM (Sb3-4-01-2)  = 479
codeM (Sb4-0-3-2)   = 480
codeM (Sb⁻4-0-3-2)  = 481
codeM (Sb4-0-12-3)  = 482
codeM (Sb4-0-2-1)   = 483
codeM (Sb4-0-3-1)   = 484
codeM (Sb⁻4-0-3-1)  = 485
codeM (Sb4-0-21-3)  = 486
codeM (Sb⁻4-0-2-1)  = 487
codeM (Sb4-0-31-2)  = 488
codeM (Sb4-1-0-2)   = 489
codeM (Sb4-1-0-3)   = 490
codeM (Sb4-1-3-2)   = 491
codeM (Sb⁻4-1-3-2)  = 492
codeM (Sb4-1-02-3)  = 493
codeM (Sb⁻4-1-0-3)  = 494
codeM (Sb4-1-23-0)  = 495
codeM (Sb⁻4-1-0-2)  = 496
codeM (Sb4-1-32-0)  = 497
codeM (Sb4-2-0-3)   = 498
codeM (Sb4-2-1-3)   = 499
codeM (Sb⁻4-2-1-3)  = 500
codeM (Sb4-2-03-1)  = 501
codeM (Sb⁻4-2-0-3)  = 502
codeM (Sb4-2-13-0)  = 503
codeM (Sb⁻2-0-41-3) = 504

tableM : List (Mac)
tableM =
  (ι) ∷
  (ι⁻) ∷
  (ι1) ∷
  (ι1⁻) ∷
  (ι2) ∷
  (ι2⁻) ∷
  (ι3) ∷
  (ι3⁻) ∷
  (ι4) ∷
  (ι4⁻) ∷
  (S0) ∷
  (S0⁻) ∷
  (K0) ∷
  (K0⁻) ∷
  (X0) ∷
  (Z0) ∷
  (S1) ∷
  (S1⁻) ∷
  (K1) ∷
  (K1⁻) ∷
  (X1) ∷
  (Z1) ∷
  (S2) ∷
  (S2⁻) ∷
  (K2) ∷
  (K2⁻) ∷
  (X2) ∷
  (Z2) ∷
  (S3) ∷
  (S3⁻) ∷
  (K3) ∷
  (K3⁻) ∷
  (X3) ∷
  (Z3) ∷
  (S4) ∷
  (S4⁻) ∷
  (K4) ∷
  (K4⁻) ∷
  (X4) ∷
  (Z4) ∷
  (CS01) ∷
  (CS01⁻) ∷
  (CZ01) ∷
  (Sw01) ∷
  (CX01) ∷
  (CK01) ∷
  (CK01⁻) ∷
  (CS02) ∷
  (CS02⁻) ∷
  (CZ02) ∷
  (Sw02) ∷
  (CX02) ∷
  (CK02) ∷
  (CK02⁻) ∷
  (CS03) ∷
  (CS03⁻) ∷
  (CZ03) ∷
  (Sw03) ∷
  (CX03) ∷
  (CK03) ∷
  (CK03⁻) ∷
  (CS04) ∷
  (CS04⁻) ∷
  (CZ04) ∷
  (Sw04) ∷
  (CX04) ∷
  (CK04) ∷
  (CK04⁻) ∷
  (CX10) ∷
  (CK10) ∷
  (CK10⁻) ∷
  (CS12) ∷
  (CS12⁻) ∷
  (CZ12) ∷
  (Sw12) ∷
  (CX12) ∷
  (CK12) ∷
  (CK12⁻) ∷
  (CS13) ∷
  (CS13⁻) ∷
  (CZ13) ∷
  (Sw13) ∷
  (CX13) ∷
  (CK13) ∷
  (CK13⁻) ∷
  (CS14) ∷
  (CS14⁻) ∷
  (CZ14) ∷
  (Sw14) ∷
  (CX14) ∷
  (CK14) ∷
  (CK14⁻) ∷
  (CX20) ∷
  (CK20) ∷
  (CK20⁻) ∷
  (CX21) ∷
  (CK21) ∷
  (CK21⁻) ∷
  (CS23) ∷
  (CS23⁻) ∷
  (CZ23) ∷
  (Sw23) ∷
  (CX23) ∷
  (CK23) ∷
  (CK23⁻) ∷
  (CS24) ∷
  (CS24⁻) ∷
  (CZ24) ∷
  (Sw24) ∷
  (CX24) ∷
  (CK24) ∷
  (CK24⁻) ∷
  (CX30) ∷
  (CK30) ∷
  (CK30⁻) ∷
  (CX31) ∷
  (CK31) ∷
  (CK31⁻) ∷
  (CX32) ∷
  (CK32) ∷
  (CK32⁻) ∷
  (CS34) ∷
  (CS34⁻) ∷
  (CZ34) ∷
  (Sw34) ∷
  (CX34) ∷
  (CK34) ∷
  (CK34⁻) ∷
  (CX40) ∷
  (CK40) ∷
  (CK40⁻) ∷
  (CX41) ∷
  (CK41) ∷
  (CK41⁻) ∷
  (CX42) ∷
  (CK42) ∷
  (CK42⁻) ∷
  (CX43) ∷
  (CK43) ∷
  (CK43⁻) ∷
  (CCZ012) ∷
  (Toff012) ∷
  (Toff102) ∷
  (Toff201) ∷
  (CCZ013) ∷
  (Toff013) ∷
  (Toff103) ∷
  (Toff301) ∷
  (CCZ014) ∷
  (Toff014) ∷
  (Toff104) ∷
  (Toff401) ∷
  (CCZ023) ∷
  (Toff023) ∷
  (Toff203) ∷
  (Toff302) ∷
  (CCZ024) ∷
  (Toff024) ∷
  (Toff204) ∷
  (Toff402) ∷
  (CCZ034) ∷
  (Toff034) ∷
  (Toff304) ∷
  (Toff403) ∷
  (CCZ123) ∷
  (Toff123) ∷
  (Toff213) ∷
  (Toff312) ∷
  (CCZ124) ∷
  (Toff124) ∷
  (Toff214) ∷
  (Toff412) ∷
  (CCZ134) ∷
  (Toff134) ∷
  (Toff314) ∷
  (Toff413) ∷
  (CCZ234) ∷
  (Toff234) ∷
  (Toff324) ∷
  (Toff423) ∷
  (Bx0-12) ∷
  (Bx1-03) ∷
  (Bx0-123) ∷
  (Bx0-14) ∷
  (Bx1-034) ∷
  (Bx0-1234) ∷
  (Bx0-13) ∷
  (Bx1-043) ∷
  (Bx0-1243) ∷
  (Bx1-024) ∷
  (Bx0-1324) ∷
  (Bx1-04) ∷
  (Bx0-134) ∷
  (Bx1-042) ∷
  (Bx0-1342) ∷
  (Bx1-023) ∷
  (Bx0-1423) ∷
  (Bx1-032) ∷
  (Bx0-1432) ∷
  (Bx0-21) ∷
  (Bx2-03) ∷
  (Bx0-213) ∷
  (Bx0-24) ∷
  (Bx2-034) ∷
  (Bx0-2134) ∷
  (Bx2-04) ∷
  (Bx0-214) ∷
  (Bx0-23) ∷
  (Bx2-043) ∷
  (Bx0-2143) ∷
  (Bx2-01) ∷
  (Bx0-231) ∷
  (Bx2-014) ∷
  (Bx0-2314) ∷
  (Bx0-234) ∷
  (Bx2-041) ∷
  (Bx0-2341) ∷
  (Bx0-241) ∷
  (Bx2-013) ∷
  (Bx0-2413) ∷
  (Bx0-243) ∷
  (Bx2-031) ∷
  (Bx0-2431) ∷
  (Bx0-31) ∷
  (Bx3-02) ∷
  (Bx0-312) ∷
  (Bx0-34) ∷
  (Bx3-024) ∷
  (Bx0-3124) ∷
  (Bx3-04) ∷
  (Bx0-314) ∷
  (Bx0-32) ∷
  (Bx3-042) ∷
  (Bx0-3142) ∷
  (Bx3-01) ∷
  (Bx0-321) ∷
  (Bx3-014) ∷
  (Bx0-3214) ∷
  (Bx0-324) ∷
  (Bx3-041) ∷
  (Bx0-3241) ∷
  (Bx0-341) ∷
  (Bx3-012) ∷
  (Bx0-3412) ∷
  (Bx0-342) ∷
  (Bx3-021) ∷
  (Bx0-3421) ∷
  (Bx0-41) ∷
  (Bx4-02) ∷
  (Bx0-412) ∷
  (Bx0-43) ∷
  (Bx4-023) ∷
  (Bx0-4123) ∷
  (Bx4-03) ∷
  (Bx0-413) ∷
  (Bx0-42) ∷
  (Bx4-032) ∷
  (Bx0-4132) ∷
  (Bx4-01) ∷
  (Bx0-421) ∷
  (Bx4-013) ∷
  (Bx0-4213) ∷
  (Bx0-423) ∷
  (Bx4-031) ∷
  (Bx0-4231) ∷
  (Bx0-431) ∷
  (Bx4-012) ∷
  (Bx0-4312) ∷
  (Bx4-021) ∷
  (Bx0-4321) ∷
  (Bx1-0234) ∷
  (Bx1-0423) ∷
  (Bx1-20) ∷
  (Bx2-14) ∷
  (Bx1-204) ∷
  (Bx2-10) ∷
  (Bx1-230) ∷
  (Bx1-234) ∷
  (Bx1-240) ∷
  (Bx2-130) ∷
  (Bx1-2430) ∷
  (Bx3-12) ∷
  (Bx1-302) ∷
  (Bx3-14) ∷
  (Bx1-304) ∷
  (Bx3-10) ∷
  (Bx1-320) ∷
  (Bx1-324) ∷
  (Bx1-340) ∷
  (Bx1-342) ∷
  (Bx4-12) ∷
  (Bx1-402) ∷
  (Bx4-13) ∷
  (Bx1-403) ∷
  (Bx4-10) ∷
  (Bx1-420) ∷
  (Bx1-43) ∷
  (Bx4-103) ∷
  (Bx1-4203) ∷
  (Bx1-423) ∷
  (Bx1-430) ∷
  (Bx2-0134) ∷
  (Bx2-0143) ∷
  (Bx2-0314) ∷
  (Bx2-0341) ∷
  (Bx2-0413) ∷
  (Bx2-0431) ∷
  (Bx2-1034) ∷
  (Bx2-1304) ∷
  (Bx2-1340) ∷
  (Bx2-1430) ∷
  (Bx2-30) ∷
  (Bx3-21) ∷
  (Bx2-301) ∷
  (Bx2-34) ∷
  (Bx3-214) ∷
  (Bx2-3014) ∷
  (Bx3-24) ∷
  (Bx2-304) ∷
  (Bx2-31) ∷
  (Bx3-241) ∷
  (Bx2-3041) ∷
  (Bx3-20) ∷
  (Bx2-310) ∷
  (Bx3-204) ∷
  (Bx2-3104) ∷
  (Bx2-314) ∷
  (Bx3-240) ∷
  (Bx2-3140) ∷
  (Bx2-340) ∷
  (Bx3-201) ∷
  (Bx2-3401) ∷
  (Bx2-341) ∷
  (Bx3-210) ∷
  (Bx2-3410) ∷
  (Bx2-40) ∷
  (Bx4-21) ∷
  (Bx2-401) ∷
  (Bx2-43) ∷
  (Bx4-213) ∷
  (Bx2-4013) ∷
  (Bx4-23) ∷
  (Bx2-403) ∷
  (Bx2-41) ∷
  (Bx4-231) ∷
  (Bx2-4031) ∷
  (Bx4-20) ∷
  (Bx2-410) ∷
  (Bx4-203) ∷
  (Bx2-4103) ∷
  (Bx4-230) ∷
  (Bx2-4130) ∷
  (Bx2-430) ∷
  (Bx4-201) ∷
  (Bx2-4301) ∷
  (Bx2-431) ∷
  (Bx3-0124) ∷
  (Bx3-0142) ∷
  (Bx3-0214) ∷
  (Bx3-0241) ∷
  (Bx3-0412) ∷
  (Bx3-0421) ∷
  (Bx3-1024) ∷
  (Bx3-1042) ∷
  (Bx3-1204) ∷
  (Bx3-1240) ∷
  (Bx3-1402) ∷
  (Bx3-1420) ∷
  (Bx3-2014) ∷
  (Bx3-2041) ∷
  (Bx3-2104) ∷
  (Bx3-2140) ∷
  (Bx3-2401) ∷
  (Bx3-2410) ∷
  (Bx3-40) ∷
  (Bx3-42) ∷
  (Bx4-312) ∷
  (Bx3-4012) ∷
  (Bx4-32) ∷
  (Bx3-402) ∷
  (Bx3-41) ∷
  (Bx4-321) ∷
  (Bx3-4021) ∷
  (Bx4-30) ∷
  (Bx3-410) ∷
  (Bx4-302) ∷
  (Bx3-4102) ∷
  (Bx3-412) ∷
  (Bx4-320) ∷
  (Bx3-4120) ∷
  (Bx3-420) ∷
  (Bx4-301) ∷
  (Bx3-4201) ∷
  (Bx4-31) ∷
  (Bx3-421) ∷
  (Bx4-310) ∷
  (Bx3-4210) ∷
  (Bx4-0123) ∷
  (Bx4-0213) ∷
  (Bx4-0231) ∷
  (Bx4-0312) ∷
  (Bx4-0321) ∷
  (Bx4-1023) ∷
  (Bx4-1203) ∷
  (Bx4-1230) ∷
  (Bx4-1302) ∷
  (Bx4-1320) ∷
  (Bx4-2031) ∷
  (Bx4-2103) ∷
  (Bx4-2130) ∷
  (Bx4-2301) ∷
  (Bx4-2310) ∷
  (Bx4-3012) ∷
  (Bx4-3021) ∷
  (Bx4-3102) ∷
  (Bx4-3120) ∷
  (Bx4-3210) ∷
  (Bx⁻2-03) ∷
  (Bx⁻0-213) ∷
  (Bx⁻2-0413) ∷
  (Sb0-1-2-3) ∷
  (Sb0-1-3-2) ∷
  (Sb⁻0-1-3-2) ∷
  (Sb0-1-42-3) ∷
  (Sb⁻0-1-2-3) ∷
  (Sb0-1-43-2) ∷
  (Sb0-2-1-3) ∷
  (Sb⁻0-2-1-3) ∷
  (Sb0-2-43-1) ∷
  (Sb0-3-1-2) ∷
  (Sb⁻0-3-1-2) ∷
  (Sb0-3-42-1) ∷
  (Sb0-4-1-2) ∷
  (Sb0-4-2-1) ∷
  (Sb0-4-3-1) ∷
  (Sb⁻0-4-3-1) ∷
  (Sb0-4-21-3) ∷
  (Sb⁻0-4-2-1) ∷
  (Sb0-4-31-2) ∷
  (Sb⁻0-4-1-2) ∷
  (Sb0-4-32-1) ∷
  (Sb1-0-3-2) ∷
  (Sb⁻1-0-3-2) ∷
  (Sb1-0-42-3) ∷
  (Sb1-2-0-3) ∷
  (Sb⁻1-2-0-3) ∷
  (Sb1-2-43-0) ∷
  (Sb1-4-3-0) ∷
  (Sb⁻1-4-3-0) ∷
  (Sb1-4-20-3) ∷
  (Sb2-0-3-1) ∷
  (Sb⁻2-0-3-1) ∷
  (Sb2-0-41-3) ∷
  (Sb2-1-0-3) ∷
  (Sb⁻2-1-0-3) ∷
  (Sb2-1-43-0) ∷
  (Sb2-4-3-1) ∷
  (Sb⁻2-4-3-1) ∷
  (Sb2-4-01-3) ∷
  (Sb2-4-3-0) ∷
  (Sb⁻2-4-3-0) ∷
  (Sb2-4-10-3) ∷
  (Sb3-0-4-2) ∷
  (Sb⁻3-0-4-2) ∷
  (Sb3-0-12-4) ∷
  (Sb3-0-2-1) ∷
  (Sb3-0-4-1) ∷
  (Sb⁻3-0-4-1) ∷
  (Sb3-0-21-4) ∷
  (Sb⁻3-0-2-1) ∷
  (Sb3-0-41-2) ∷
  (Sb3-1-0-2) ∷
  (Sb3-1-4-2) ∷
  (Sb⁻3-1-4-2) ∷
  (Sb3-1-02-4) ∷
  (Sb⁻3-1-0-2) ∷
  (Sb3-1-42-0) ∷
  (Sb3-4-2-1) ∷
  (Sb⁻3-4-2-1) ∷
  (Sb3-4-01-2) ∷
  (Sb4-0-3-2) ∷
  (Sb⁻4-0-3-2) ∷
  (Sb4-0-12-3) ∷
  (Sb4-0-2-1) ∷
  (Sb4-0-3-1) ∷
  (Sb⁻4-0-3-1) ∷
  (Sb4-0-21-3) ∷
  (Sb⁻4-0-2-1) ∷
  (Sb4-0-31-2) ∷
  (Sb4-1-0-2) ∷
  (Sb4-1-0-3) ∷
  (Sb4-1-3-2) ∷
  (Sb⁻4-1-3-2) ∷
  (Sb4-1-02-3) ∷
  (Sb⁻4-1-0-3) ∷
  (Sb4-1-23-0) ∷
  (Sb⁻4-1-0-2) ∷
  (Sb4-1-32-0) ∷
  (Sb4-2-0-3) ∷
  (Sb4-2-1-3) ∷
  (Sb⁻4-2-1-3) ∷
  (Sb4-2-03-1) ∷
  (Sb⁻4-2-0-3) ∷
  (Sb4-2-13-0) ∷
  (Sb⁻2-0-41-3) ∷
  []

decodeM : ℕ → Mac
decodeM n = ix (ι) tableM n

decode-codeM : ∀ x → decodeM (codeM x) ≡ x
decode-codeM (ι)           = Eq.refl
decode-codeM (ι⁻)          = Eq.refl
decode-codeM (ι1)          = Eq.refl
decode-codeM (ι1⁻)         = Eq.refl
decode-codeM (ι2)          = Eq.refl
decode-codeM (ι2⁻)         = Eq.refl
decode-codeM (ι3)          = Eq.refl
decode-codeM (ι3⁻)         = Eq.refl
decode-codeM (ι4)          = Eq.refl
decode-codeM (ι4⁻)         = Eq.refl
decode-codeM (S0)          = Eq.refl
decode-codeM (S0⁻)         = Eq.refl
decode-codeM (K0)          = Eq.refl
decode-codeM (K0⁻)         = Eq.refl
decode-codeM (X0)          = Eq.refl
decode-codeM (Z0)          = Eq.refl
decode-codeM (S1)          = Eq.refl
decode-codeM (S1⁻)         = Eq.refl
decode-codeM (K1)          = Eq.refl
decode-codeM (K1⁻)         = Eq.refl
decode-codeM (X1)          = Eq.refl
decode-codeM (Z1)          = Eq.refl
decode-codeM (S2)          = Eq.refl
decode-codeM (S2⁻)         = Eq.refl
decode-codeM (K2)          = Eq.refl
decode-codeM (K2⁻)         = Eq.refl
decode-codeM (X2)          = Eq.refl
decode-codeM (Z2)          = Eq.refl
decode-codeM (S3)          = Eq.refl
decode-codeM (S3⁻)         = Eq.refl
decode-codeM (K3)          = Eq.refl
decode-codeM (K3⁻)         = Eq.refl
decode-codeM (X3)          = Eq.refl
decode-codeM (Z3)          = Eq.refl
decode-codeM (S4)          = Eq.refl
decode-codeM (S4⁻)         = Eq.refl
decode-codeM (K4)          = Eq.refl
decode-codeM (K4⁻)         = Eq.refl
decode-codeM (X4)          = Eq.refl
decode-codeM (Z4)          = Eq.refl
decode-codeM (CS01)        = Eq.refl
decode-codeM (CS01⁻)       = Eq.refl
decode-codeM (CZ01)        = Eq.refl
decode-codeM (Sw01)        = Eq.refl
decode-codeM (CX01)        = Eq.refl
decode-codeM (CK01)        = Eq.refl
decode-codeM (CK01⁻)       = Eq.refl
decode-codeM (CS02)        = Eq.refl
decode-codeM (CS02⁻)       = Eq.refl
decode-codeM (CZ02)        = Eq.refl
decode-codeM (Sw02)        = Eq.refl
decode-codeM (CX02)        = Eq.refl
decode-codeM (CK02)        = Eq.refl
decode-codeM (CK02⁻)       = Eq.refl
decode-codeM (CS03)        = Eq.refl
decode-codeM (CS03⁻)       = Eq.refl
decode-codeM (CZ03)        = Eq.refl
decode-codeM (Sw03)        = Eq.refl
decode-codeM (CX03)        = Eq.refl
decode-codeM (CK03)        = Eq.refl
decode-codeM (CK03⁻)       = Eq.refl
decode-codeM (CS04)        = Eq.refl
decode-codeM (CS04⁻)       = Eq.refl
decode-codeM (CZ04)        = Eq.refl
decode-codeM (Sw04)        = Eq.refl
decode-codeM (CX04)        = Eq.refl
decode-codeM (CK04)        = Eq.refl
decode-codeM (CK04⁻)       = Eq.refl
decode-codeM (CX10)        = Eq.refl
decode-codeM (CK10)        = Eq.refl
decode-codeM (CK10⁻)       = Eq.refl
decode-codeM (CS12)        = Eq.refl
decode-codeM (CS12⁻)       = Eq.refl
decode-codeM (CZ12)        = Eq.refl
decode-codeM (Sw12)        = Eq.refl
decode-codeM (CX12)        = Eq.refl
decode-codeM (CK12)        = Eq.refl
decode-codeM (CK12⁻)       = Eq.refl
decode-codeM (CS13)        = Eq.refl
decode-codeM (CS13⁻)       = Eq.refl
decode-codeM (CZ13)        = Eq.refl
decode-codeM (Sw13)        = Eq.refl
decode-codeM (CX13)        = Eq.refl
decode-codeM (CK13)        = Eq.refl
decode-codeM (CK13⁻)       = Eq.refl
decode-codeM (CS14)        = Eq.refl
decode-codeM (CS14⁻)       = Eq.refl
decode-codeM (CZ14)        = Eq.refl
decode-codeM (Sw14)        = Eq.refl
decode-codeM (CX14)        = Eq.refl
decode-codeM (CK14)        = Eq.refl
decode-codeM (CK14⁻)       = Eq.refl
decode-codeM (CX20)        = Eq.refl
decode-codeM (CK20)        = Eq.refl
decode-codeM (CK20⁻)       = Eq.refl
decode-codeM (CX21)        = Eq.refl
decode-codeM (CK21)        = Eq.refl
decode-codeM (CK21⁻)       = Eq.refl
decode-codeM (CS23)        = Eq.refl
decode-codeM (CS23⁻)       = Eq.refl
decode-codeM (CZ23)        = Eq.refl
decode-codeM (Sw23)        = Eq.refl
decode-codeM (CX23)        = Eq.refl
decode-codeM (CK23)        = Eq.refl
decode-codeM (CK23⁻)       = Eq.refl
decode-codeM (CS24)        = Eq.refl
decode-codeM (CS24⁻)       = Eq.refl
decode-codeM (CZ24)        = Eq.refl
decode-codeM (Sw24)        = Eq.refl
decode-codeM (CX24)        = Eq.refl
decode-codeM (CK24)        = Eq.refl
decode-codeM (CK24⁻)       = Eq.refl
decode-codeM (CX30)        = Eq.refl
decode-codeM (CK30)        = Eq.refl
decode-codeM (CK30⁻)       = Eq.refl
decode-codeM (CX31)        = Eq.refl
decode-codeM (CK31)        = Eq.refl
decode-codeM (CK31⁻)       = Eq.refl
decode-codeM (CX32)        = Eq.refl
decode-codeM (CK32)        = Eq.refl
decode-codeM (CK32⁻)       = Eq.refl
decode-codeM (CS34)        = Eq.refl
decode-codeM (CS34⁻)       = Eq.refl
decode-codeM (CZ34)        = Eq.refl
decode-codeM (Sw34)        = Eq.refl
decode-codeM (CX34)        = Eq.refl
decode-codeM (CK34)        = Eq.refl
decode-codeM (CK34⁻)       = Eq.refl
decode-codeM (CX40)        = Eq.refl
decode-codeM (CK40)        = Eq.refl
decode-codeM (CK40⁻)       = Eq.refl
decode-codeM (CX41)        = Eq.refl
decode-codeM (CK41)        = Eq.refl
decode-codeM (CK41⁻)       = Eq.refl
decode-codeM (CX42)        = Eq.refl
decode-codeM (CK42)        = Eq.refl
decode-codeM (CK42⁻)       = Eq.refl
decode-codeM (CX43)        = Eq.refl
decode-codeM (CK43)        = Eq.refl
decode-codeM (CK43⁻)       = Eq.refl
decode-codeM (CCZ012)      = Eq.refl
decode-codeM (Toff012)     = Eq.refl
decode-codeM (Toff102)     = Eq.refl
decode-codeM (Toff201)     = Eq.refl
decode-codeM (CCZ013)      = Eq.refl
decode-codeM (Toff013)     = Eq.refl
decode-codeM (Toff103)     = Eq.refl
decode-codeM (Toff301)     = Eq.refl
decode-codeM (CCZ014)      = Eq.refl
decode-codeM (Toff014)     = Eq.refl
decode-codeM (Toff104)     = Eq.refl
decode-codeM (Toff401)     = Eq.refl
decode-codeM (CCZ023)      = Eq.refl
decode-codeM (Toff023)     = Eq.refl
decode-codeM (Toff203)     = Eq.refl
decode-codeM (Toff302)     = Eq.refl
decode-codeM (CCZ024)      = Eq.refl
decode-codeM (Toff024)     = Eq.refl
decode-codeM (Toff204)     = Eq.refl
decode-codeM (Toff402)     = Eq.refl
decode-codeM (CCZ034)      = Eq.refl
decode-codeM (Toff034)     = Eq.refl
decode-codeM (Toff304)     = Eq.refl
decode-codeM (Toff403)     = Eq.refl
decode-codeM (CCZ123)      = Eq.refl
decode-codeM (Toff123)     = Eq.refl
decode-codeM (Toff213)     = Eq.refl
decode-codeM (Toff312)     = Eq.refl
decode-codeM (CCZ124)      = Eq.refl
decode-codeM (Toff124)     = Eq.refl
decode-codeM (Toff214)     = Eq.refl
decode-codeM (Toff412)     = Eq.refl
decode-codeM (CCZ134)      = Eq.refl
decode-codeM (Toff134)     = Eq.refl
decode-codeM (Toff314)     = Eq.refl
decode-codeM (Toff413)     = Eq.refl
decode-codeM (CCZ234)      = Eq.refl
decode-codeM (Toff234)     = Eq.refl
decode-codeM (Toff324)     = Eq.refl
decode-codeM (Toff423)     = Eq.refl
decode-codeM (Bx0-12)      = Eq.refl
decode-codeM (Bx1-03)      = Eq.refl
decode-codeM (Bx0-123)     = Eq.refl
decode-codeM (Bx0-14)      = Eq.refl
decode-codeM (Bx1-034)     = Eq.refl
decode-codeM (Bx0-1234)    = Eq.refl
decode-codeM (Bx0-13)      = Eq.refl
decode-codeM (Bx1-043)     = Eq.refl
decode-codeM (Bx0-1243)    = Eq.refl
decode-codeM (Bx1-024)     = Eq.refl
decode-codeM (Bx0-1324)    = Eq.refl
decode-codeM (Bx1-04)      = Eq.refl
decode-codeM (Bx0-134)     = Eq.refl
decode-codeM (Bx1-042)     = Eq.refl
decode-codeM (Bx0-1342)    = Eq.refl
decode-codeM (Bx1-023)     = Eq.refl
decode-codeM (Bx0-1423)    = Eq.refl
decode-codeM (Bx1-032)     = Eq.refl
decode-codeM (Bx0-1432)    = Eq.refl
decode-codeM (Bx0-21)      = Eq.refl
decode-codeM (Bx2-03)      = Eq.refl
decode-codeM (Bx0-213)     = Eq.refl
decode-codeM (Bx0-24)      = Eq.refl
decode-codeM (Bx2-034)     = Eq.refl
decode-codeM (Bx0-2134)    = Eq.refl
decode-codeM (Bx2-04)      = Eq.refl
decode-codeM (Bx0-214)     = Eq.refl
decode-codeM (Bx0-23)      = Eq.refl
decode-codeM (Bx2-043)     = Eq.refl
decode-codeM (Bx0-2143)    = Eq.refl
decode-codeM (Bx2-01)      = Eq.refl
decode-codeM (Bx0-231)     = Eq.refl
decode-codeM (Bx2-014)     = Eq.refl
decode-codeM (Bx0-2314)    = Eq.refl
decode-codeM (Bx0-234)     = Eq.refl
decode-codeM (Bx2-041)     = Eq.refl
decode-codeM (Bx0-2341)    = Eq.refl
decode-codeM (Bx0-241)     = Eq.refl
decode-codeM (Bx2-013)     = Eq.refl
decode-codeM (Bx0-2413)    = Eq.refl
decode-codeM (Bx0-243)     = Eq.refl
decode-codeM (Bx2-031)     = Eq.refl
decode-codeM (Bx0-2431)    = Eq.refl
decode-codeM (Bx0-31)      = Eq.refl
decode-codeM (Bx3-02)      = Eq.refl
decode-codeM (Bx0-312)     = Eq.refl
decode-codeM (Bx0-34)      = Eq.refl
decode-codeM (Bx3-024)     = Eq.refl
decode-codeM (Bx0-3124)    = Eq.refl
decode-codeM (Bx3-04)      = Eq.refl
decode-codeM (Bx0-314)     = Eq.refl
decode-codeM (Bx0-32)      = Eq.refl
decode-codeM (Bx3-042)     = Eq.refl
decode-codeM (Bx0-3142)    = Eq.refl
decode-codeM (Bx3-01)      = Eq.refl
decode-codeM (Bx0-321)     = Eq.refl
decode-codeM (Bx3-014)     = Eq.refl
decode-codeM (Bx0-3214)    = Eq.refl
decode-codeM (Bx0-324)     = Eq.refl
decode-codeM (Bx3-041)     = Eq.refl
decode-codeM (Bx0-3241)    = Eq.refl
decode-codeM (Bx0-341)     = Eq.refl
decode-codeM (Bx3-012)     = Eq.refl
decode-codeM (Bx0-3412)    = Eq.refl
decode-codeM (Bx0-342)     = Eq.refl
decode-codeM (Bx3-021)     = Eq.refl
decode-codeM (Bx0-3421)    = Eq.refl
decode-codeM (Bx0-41)      = Eq.refl
decode-codeM (Bx4-02)      = Eq.refl
decode-codeM (Bx0-412)     = Eq.refl
decode-codeM (Bx0-43)      = Eq.refl
decode-codeM (Bx4-023)     = Eq.refl
decode-codeM (Bx0-4123)    = Eq.refl
decode-codeM (Bx4-03)      = Eq.refl
decode-codeM (Bx0-413)     = Eq.refl
decode-codeM (Bx0-42)      = Eq.refl
decode-codeM (Bx4-032)     = Eq.refl
decode-codeM (Bx0-4132)    = Eq.refl
decode-codeM (Bx4-01)      = Eq.refl
decode-codeM (Bx0-421)     = Eq.refl
decode-codeM (Bx4-013)     = Eq.refl
decode-codeM (Bx0-4213)    = Eq.refl
decode-codeM (Bx0-423)     = Eq.refl
decode-codeM (Bx4-031)     = Eq.refl
decode-codeM (Bx0-4231)    = Eq.refl
decode-codeM (Bx0-431)     = Eq.refl
decode-codeM (Bx4-012)     = Eq.refl
decode-codeM (Bx0-4312)    = Eq.refl
decode-codeM (Bx4-021)     = Eq.refl
decode-codeM (Bx0-4321)    = Eq.refl
decode-codeM (Bx1-0234)    = Eq.refl
decode-codeM (Bx1-0423)    = Eq.refl
decode-codeM (Bx1-20)      = Eq.refl
decode-codeM (Bx2-14)      = Eq.refl
decode-codeM (Bx1-204)     = Eq.refl
decode-codeM (Bx2-10)      = Eq.refl
decode-codeM (Bx1-230)     = Eq.refl
decode-codeM (Bx1-234)     = Eq.refl
decode-codeM (Bx1-240)     = Eq.refl
decode-codeM (Bx2-130)     = Eq.refl
decode-codeM (Bx1-2430)    = Eq.refl
decode-codeM (Bx3-12)      = Eq.refl
decode-codeM (Bx1-302)     = Eq.refl
decode-codeM (Bx3-14)      = Eq.refl
decode-codeM (Bx1-304)     = Eq.refl
decode-codeM (Bx3-10)      = Eq.refl
decode-codeM (Bx1-320)     = Eq.refl
decode-codeM (Bx1-324)     = Eq.refl
decode-codeM (Bx1-340)     = Eq.refl
decode-codeM (Bx1-342)     = Eq.refl
decode-codeM (Bx4-12)      = Eq.refl
decode-codeM (Bx1-402)     = Eq.refl
decode-codeM (Bx4-13)      = Eq.refl
decode-codeM (Bx1-403)     = Eq.refl
decode-codeM (Bx4-10)      = Eq.refl
decode-codeM (Bx1-420)     = Eq.refl
decode-codeM (Bx1-43)      = Eq.refl
decode-codeM (Bx4-103)     = Eq.refl
decode-codeM (Bx1-4203)    = Eq.refl
decode-codeM (Bx1-423)     = Eq.refl
decode-codeM (Bx1-430)     = Eq.refl
decode-codeM (Bx2-0134)    = Eq.refl
decode-codeM (Bx2-0143)    = Eq.refl
decode-codeM (Bx2-0314)    = Eq.refl
decode-codeM (Bx2-0341)    = Eq.refl
decode-codeM (Bx2-0413)    = Eq.refl
decode-codeM (Bx2-0431)    = Eq.refl
decode-codeM (Bx2-1034)    = Eq.refl
decode-codeM (Bx2-1304)    = Eq.refl
decode-codeM (Bx2-1340)    = Eq.refl
decode-codeM (Bx2-1430)    = Eq.refl
decode-codeM (Bx2-30)      = Eq.refl
decode-codeM (Bx3-21)      = Eq.refl
decode-codeM (Bx2-301)     = Eq.refl
decode-codeM (Bx2-34)      = Eq.refl
decode-codeM (Bx3-214)     = Eq.refl
decode-codeM (Bx2-3014)    = Eq.refl
decode-codeM (Bx3-24)      = Eq.refl
decode-codeM (Bx2-304)     = Eq.refl
decode-codeM (Bx2-31)      = Eq.refl
decode-codeM (Bx3-241)     = Eq.refl
decode-codeM (Bx2-3041)    = Eq.refl
decode-codeM (Bx3-20)      = Eq.refl
decode-codeM (Bx2-310)     = Eq.refl
decode-codeM (Bx3-204)     = Eq.refl
decode-codeM (Bx2-3104)    = Eq.refl
decode-codeM (Bx2-314)     = Eq.refl
decode-codeM (Bx3-240)     = Eq.refl
decode-codeM (Bx2-3140)    = Eq.refl
decode-codeM (Bx2-340)     = Eq.refl
decode-codeM (Bx3-201)     = Eq.refl
decode-codeM (Bx2-3401)    = Eq.refl
decode-codeM (Bx2-341)     = Eq.refl
decode-codeM (Bx3-210)     = Eq.refl
decode-codeM (Bx2-3410)    = Eq.refl
decode-codeM (Bx2-40)      = Eq.refl
decode-codeM (Bx4-21)      = Eq.refl
decode-codeM (Bx2-401)     = Eq.refl
decode-codeM (Bx2-43)      = Eq.refl
decode-codeM (Bx4-213)     = Eq.refl
decode-codeM (Bx2-4013)    = Eq.refl
decode-codeM (Bx4-23)      = Eq.refl
decode-codeM (Bx2-403)     = Eq.refl
decode-codeM (Bx2-41)      = Eq.refl
decode-codeM (Bx4-231)     = Eq.refl
decode-codeM (Bx2-4031)    = Eq.refl
decode-codeM (Bx4-20)      = Eq.refl
decode-codeM (Bx2-410)     = Eq.refl
decode-codeM (Bx4-203)     = Eq.refl
decode-codeM (Bx2-4103)    = Eq.refl
decode-codeM (Bx4-230)     = Eq.refl
decode-codeM (Bx2-4130)    = Eq.refl
decode-codeM (Bx2-430)     = Eq.refl
decode-codeM (Bx4-201)     = Eq.refl
decode-codeM (Bx2-4301)    = Eq.refl
decode-codeM (Bx2-431)     = Eq.refl
decode-codeM (Bx3-0124)    = Eq.refl
decode-codeM (Bx3-0142)    = Eq.refl
decode-codeM (Bx3-0214)    = Eq.refl
decode-codeM (Bx3-0241)    = Eq.refl
decode-codeM (Bx3-0412)    = Eq.refl
decode-codeM (Bx3-0421)    = Eq.refl
decode-codeM (Bx3-1024)    = Eq.refl
decode-codeM (Bx3-1042)    = Eq.refl
decode-codeM (Bx3-1204)    = Eq.refl
decode-codeM (Bx3-1240)    = Eq.refl
decode-codeM (Bx3-1402)    = Eq.refl
decode-codeM (Bx3-1420)    = Eq.refl
decode-codeM (Bx3-2014)    = Eq.refl
decode-codeM (Bx3-2041)    = Eq.refl
decode-codeM (Bx3-2104)    = Eq.refl
decode-codeM (Bx3-2140)    = Eq.refl
decode-codeM (Bx3-2401)    = Eq.refl
decode-codeM (Bx3-2410)    = Eq.refl
decode-codeM (Bx3-40)      = Eq.refl
decode-codeM (Bx3-42)      = Eq.refl
decode-codeM (Bx4-312)     = Eq.refl
decode-codeM (Bx3-4012)    = Eq.refl
decode-codeM (Bx4-32)      = Eq.refl
decode-codeM (Bx3-402)     = Eq.refl
decode-codeM (Bx3-41)      = Eq.refl
decode-codeM (Bx4-321)     = Eq.refl
decode-codeM (Bx3-4021)    = Eq.refl
decode-codeM (Bx4-30)      = Eq.refl
decode-codeM (Bx3-410)     = Eq.refl
decode-codeM (Bx4-302)     = Eq.refl
decode-codeM (Bx3-4102)    = Eq.refl
decode-codeM (Bx3-412)     = Eq.refl
decode-codeM (Bx4-320)     = Eq.refl
decode-codeM (Bx3-4120)    = Eq.refl
decode-codeM (Bx3-420)     = Eq.refl
decode-codeM (Bx4-301)     = Eq.refl
decode-codeM (Bx3-4201)    = Eq.refl
decode-codeM (Bx4-31)      = Eq.refl
decode-codeM (Bx3-421)     = Eq.refl
decode-codeM (Bx4-310)     = Eq.refl
decode-codeM (Bx3-4210)    = Eq.refl
decode-codeM (Bx4-0123)    = Eq.refl
decode-codeM (Bx4-0213)    = Eq.refl
decode-codeM (Bx4-0231)    = Eq.refl
decode-codeM (Bx4-0312)    = Eq.refl
decode-codeM (Bx4-0321)    = Eq.refl
decode-codeM (Bx4-1023)    = Eq.refl
decode-codeM (Bx4-1203)    = Eq.refl
decode-codeM (Bx4-1230)    = Eq.refl
decode-codeM (Bx4-1302)    = Eq.refl
decode-codeM (Bx4-1320)    = Eq.refl
decode-codeM (Bx4-2031)    = Eq.refl
decode-codeM (Bx4-2103)    = Eq.refl
decode-codeM (Bx4-2130)    = Eq.refl
decode-codeM (Bx4-2301)    = Eq.refl
decode-codeM (Bx4-2310)    = Eq.refl
decode-codeM (Bx4-3012)    = Eq.refl
decode-codeM (Bx4-3021)    = Eq.refl
decode-codeM (Bx4-3102)    = Eq.refl
decode-codeM (Bx4-3120)    = Eq.refl
decode-codeM (Bx4-3210)    = Eq.refl
decode-codeM (Bx⁻2-03)     = Eq.refl
decode-codeM (Bx⁻0-213)    = Eq.refl
decode-codeM (Bx⁻2-0413)   = Eq.refl
decode-codeM (Sb0-1-2-3)   = Eq.refl
decode-codeM (Sb0-1-3-2)   = Eq.refl
decode-codeM (Sb⁻0-1-3-2)  = Eq.refl
decode-codeM (Sb0-1-42-3)  = Eq.refl
decode-codeM (Sb⁻0-1-2-3)  = Eq.refl
decode-codeM (Sb0-1-43-2)  = Eq.refl
decode-codeM (Sb0-2-1-3)   = Eq.refl
decode-codeM (Sb⁻0-2-1-3)  = Eq.refl
decode-codeM (Sb0-2-43-1)  = Eq.refl
decode-codeM (Sb0-3-1-2)   = Eq.refl
decode-codeM (Sb⁻0-3-1-2)  = Eq.refl
decode-codeM (Sb0-3-42-1)  = Eq.refl
decode-codeM (Sb0-4-1-2)   = Eq.refl
decode-codeM (Sb0-4-2-1)   = Eq.refl
decode-codeM (Sb0-4-3-1)   = Eq.refl
decode-codeM (Sb⁻0-4-3-1)  = Eq.refl
decode-codeM (Sb0-4-21-3)  = Eq.refl
decode-codeM (Sb⁻0-4-2-1)  = Eq.refl
decode-codeM (Sb0-4-31-2)  = Eq.refl
decode-codeM (Sb⁻0-4-1-2)  = Eq.refl
decode-codeM (Sb0-4-32-1)  = Eq.refl
decode-codeM (Sb1-0-3-2)   = Eq.refl
decode-codeM (Sb⁻1-0-3-2)  = Eq.refl
decode-codeM (Sb1-0-42-3)  = Eq.refl
decode-codeM (Sb1-2-0-3)   = Eq.refl
decode-codeM (Sb⁻1-2-0-3)  = Eq.refl
decode-codeM (Sb1-2-43-0)  = Eq.refl
decode-codeM (Sb1-4-3-0)   = Eq.refl
decode-codeM (Sb⁻1-4-3-0)  = Eq.refl
decode-codeM (Sb1-4-20-3)  = Eq.refl
decode-codeM (Sb2-0-3-1)   = Eq.refl
decode-codeM (Sb⁻2-0-3-1)  = Eq.refl
decode-codeM (Sb2-0-41-3)  = Eq.refl
decode-codeM (Sb2-1-0-3)   = Eq.refl
decode-codeM (Sb⁻2-1-0-3)  = Eq.refl
decode-codeM (Sb2-1-43-0)  = Eq.refl
decode-codeM (Sb2-4-3-1)   = Eq.refl
decode-codeM (Sb⁻2-4-3-1)  = Eq.refl
decode-codeM (Sb2-4-01-3)  = Eq.refl
decode-codeM (Sb2-4-3-0)   = Eq.refl
decode-codeM (Sb⁻2-4-3-0)  = Eq.refl
decode-codeM (Sb2-4-10-3)  = Eq.refl
decode-codeM (Sb3-0-4-2)   = Eq.refl
decode-codeM (Sb⁻3-0-4-2)  = Eq.refl
decode-codeM (Sb3-0-12-4)  = Eq.refl
decode-codeM (Sb3-0-2-1)   = Eq.refl
decode-codeM (Sb3-0-4-1)   = Eq.refl
decode-codeM (Sb⁻3-0-4-1)  = Eq.refl
decode-codeM (Sb3-0-21-4)  = Eq.refl
decode-codeM (Sb⁻3-0-2-1)  = Eq.refl
decode-codeM (Sb3-0-41-2)  = Eq.refl
decode-codeM (Sb3-1-0-2)   = Eq.refl
decode-codeM (Sb3-1-4-2)   = Eq.refl
decode-codeM (Sb⁻3-1-4-2)  = Eq.refl
decode-codeM (Sb3-1-02-4)  = Eq.refl
decode-codeM (Sb⁻3-1-0-2)  = Eq.refl
decode-codeM (Sb3-1-42-0)  = Eq.refl
decode-codeM (Sb3-4-2-1)   = Eq.refl
decode-codeM (Sb⁻3-4-2-1)  = Eq.refl
decode-codeM (Sb3-4-01-2)  = Eq.refl
decode-codeM (Sb4-0-3-2)   = Eq.refl
decode-codeM (Sb⁻4-0-3-2)  = Eq.refl
decode-codeM (Sb4-0-12-3)  = Eq.refl
decode-codeM (Sb4-0-2-1)   = Eq.refl
decode-codeM (Sb4-0-3-1)   = Eq.refl
decode-codeM (Sb⁻4-0-3-1)  = Eq.refl
decode-codeM (Sb4-0-21-3)  = Eq.refl
decode-codeM (Sb⁻4-0-2-1)  = Eq.refl
decode-codeM (Sb4-0-31-2)  = Eq.refl
decode-codeM (Sb4-1-0-2)   = Eq.refl
decode-codeM (Sb4-1-0-3)   = Eq.refl
decode-codeM (Sb4-1-3-2)   = Eq.refl
decode-codeM (Sb⁻4-1-3-2)  = Eq.refl
decode-codeM (Sb4-1-02-3)  = Eq.refl
decode-codeM (Sb⁻4-1-0-3)  = Eq.refl
decode-codeM (Sb4-1-23-0)  = Eq.refl
decode-codeM (Sb⁻4-1-0-2)  = Eq.refl
decode-codeM (Sb4-1-32-0)  = Eq.refl
decode-codeM (Sb4-2-0-3)   = Eq.refl
decode-codeM (Sb4-2-1-3)   = Eq.refl
decode-codeM (Sb⁻4-2-1-3)  = Eq.refl
decode-codeM (Sb4-2-03-1)  = Eq.refl
decode-codeM (Sb⁻4-2-0-3)  = Eq.refl
decode-codeM (Sb4-2-13-0)  = Eq.refl
decode-codeM (Sb⁻2-0-41-3) = Eq.refl

codeG : Gen 5 → ℕ
codeG (gate₀ I-gate)           = 0
codeG (gate₀ I-gate ↥)         = 1
codeG (gate₀ I-gate ↥ ↥)       = 2
codeG (gate₀ I-gate ↥ ↥ ↥)     = 3
codeG (gate₀ I-gate ↥ ↥ ↥ ↥)   = 4
codeG (gate₀ I-gate ↥ ↥ ↥ ↥ ↥) = 5
codeG (gate₁ S-gate)           = 6
codeG (gate₁ K-gate)           = 7
codeG (gate₁ S-gate ↥)         = 8
codeG (gate₁ K-gate ↥)         = 9
codeG (gate₁ S-gate ↥ ↥)       = 10
codeG (gate₁ K-gate ↥ ↥)       = 11
codeG (gate₁ S-gate ↥ ↥ ↥)     = 12
codeG (gate₁ K-gate ↥ ↥ ↥)     = 13
codeG (gate₁ S-gate ↥ ↥ ↥ ↥)   = 14
codeG (gate₁ K-gate ↥ ↥ ↥ ↥)   = 15
codeG (gate₂ CS-gate)          = 16
codeG (gate₂ CS-gate ↥)        = 17
codeG (gate₂ CS-gate ↥ ↥)      = 18
codeG (gate₂ CS-gate ↥ ↥ ↥)    = 19

tableG : List (Gen 5)
tableG =
  (gate₀ I-gate) ∷
  (gate₀ I-gate ↥) ∷
  (gate₀ I-gate ↥ ↥) ∷
  (gate₀ I-gate ↥ ↥ ↥) ∷
  (gate₀ I-gate ↥ ↥ ↥ ↥) ∷
  (gate₀ I-gate ↥ ↥ ↥ ↥ ↥) ∷
  (gate₁ S-gate) ∷
  (gate₁ K-gate) ∷
  (gate₁ S-gate ↥) ∷
  (gate₁ K-gate ↥) ∷
  (gate₁ S-gate ↥ ↥) ∷
  (gate₁ K-gate ↥ ↥) ∷
  (gate₁ S-gate ↥ ↥ ↥) ∷
  (gate₁ K-gate ↥ ↥ ↥) ∷
  (gate₁ S-gate ↥ ↥ ↥ ↥) ∷
  (gate₁ K-gate ↥ ↥ ↥ ↥) ∷
  (gate₂ CS-gate) ∷
  (gate₂ CS-gate ↥) ∷
  (gate₂ CS-gate ↥ ↥) ∷
  (gate₂ CS-gate ↥ ↥ ↥) ∷
  []

decodeG : ℕ → Gen 5
decodeG n = ix (gate₀ I-gate) tableG n

decode-codeG : ∀ x → decodeG (codeG x) ≡ x
decode-codeG (gate₀ I-gate)           = Eq.refl
decode-codeG (gate₀ I-gate ↥)         = Eq.refl
decode-codeG (gate₀ I-gate ↥ ↥)       = Eq.refl
decode-codeG (gate₀ I-gate ↥ ↥ ↥)     = Eq.refl
decode-codeG (gate₀ I-gate ↥ ↥ ↥ ↥)   = Eq.refl
decode-codeG (gate₀ I-gate ↥ ↥ ↥ ↥ ↥) = Eq.refl
decode-codeG (gate₁ S-gate)           = Eq.refl
decode-codeG (gate₁ K-gate)           = Eq.refl
decode-codeG (gate₁ S-gate ↥)         = Eq.refl
decode-codeG (gate₁ K-gate ↥)         = Eq.refl
decode-codeG (gate₁ S-gate ↥ ↥)       = Eq.refl
decode-codeG (gate₁ K-gate ↥ ↥)       = Eq.refl
decode-codeG (gate₁ S-gate ↥ ↥ ↥)     = Eq.refl
decode-codeG (gate₁ K-gate ↥ ↥ ↥)     = Eq.refl
decode-codeG (gate₁ S-gate ↥ ↥ ↥ ↥)   = Eq.refl
decode-codeG (gate₁ K-gate ↥ ↥ ↥ ↥)   = Eq.refl
decode-codeG (gate₂ CS-gate)          = Eq.refl
decode-codeG (gate₂ CS-gate ↥)        = Eq.refl
decode-codeG (gate₂ CS-gate ↥ ↥)      = Eq.refl
decode-codeG (gate₂ CS-gate ↥ ↥ ↥)    = Eq.refl

private
  ≡ᵇ-sound : ∀ x y → (x ≡ᵇ y) ≡ true → x ≡ y
  ≡ᵇ-sound x y h = ≡ᵇ⇒≡ x y (Eq.subst T (Eq.sym h) tt)

eqLM : List Mac → List Mac → Bool
eqLM []       []       = true
eqLM []       (y ∷ ys) = false
eqLM (x ∷ xs) []       = false
eqLM (x ∷ xs) (y ∷ ys) = (codeM x ≡ᵇ codeM y) ∧ eqLM xs ys

eqLM-sound : (xs ys : List Mac) → eqLM xs ys ≡ true → xs ≡ ys
eqLM-sound []       []       h = Eq.refl
eqLM-sound []       (y ∷ ys) ()
eqLM-sound (x ∷ xs) []       ()
eqLM-sound (x ∷ xs) (y ∷ ys) h with codeM x ≡ᵇ codeM y in e
eqLM-sound (x ∷ xs) (y ∷ ys) h  | true  =
  Eq.cong₂ _∷_
    (Eq.trans (Eq.sym (decode-codeM x))
      (Eq.trans (Eq.cong decodeM (≡ᵇ-sound (codeM x) (codeM y) e)) (decode-codeM y)))
    (eqLM-sound xs ys h)
eqLM-sound (x ∷ xs) (y ∷ ys) () | false

eqLG : List (Gen 5) → List (Gen 5) → Bool
eqLG []       []       = true
eqLG []       (y ∷ ys) = false
eqLG (x ∷ xs) []       = false
eqLG (x ∷ xs) (y ∷ ys) = (codeG x ≡ᵇ codeG y) ∧ eqLG xs ys

eqLG-sound : (xs ys : List (Gen 5)) → eqLG xs ys ≡ true → xs ≡ ys
eqLG-sound []       []       h = Eq.refl
eqLG-sound []       (y ∷ ys) ()
eqLG-sound (x ∷ xs) []       ()
eqLG-sound (x ∷ xs) (y ∷ ys) h with codeG x ≡ᵇ codeG y in e
eqLG-sound (x ∷ xs) (y ∷ ys) h  | true  =
  Eq.cong₂ _∷_
    (Eq.trans (Eq.sym (decode-codeG x))
      (Eq.trans (Eq.cong decodeG (≡ᵇ-sound (codeG x) (codeG y) e)) (decode-codeG y)))
    (eqLG-sound xs ys h)
eqLG-sound (x ∷ xs) (y ∷ ys) () | false

------------------------------------------------------------------------
-- Equations and steps

record Eqn : Set where
  constructor eqn
  field
    lhs rhs : List Mac
    prf     : ⟪ lhs ⟫ʷ ≈ ⟪ rhs ⟫ʷ

open Eqn public

data Step : Set where
  rw rw⁻ : ℕ → Eqn → Step
  re     : ℕ → ℕ → List Mac → Step

flat : List Mac → List (Gen 5)
flat ms = to-list ⟪ ms ⟫ʷ

------------------------------------------------------------------------
-- Each letter as atoms

-- A re-bracketing compared the generators its two sides spell, four
-- hundred a letter on average here: about 14 ms a step, most of the
-- time of running a long Five/D derivation.  Each letter is also a
-- list of atoms -- CCZ and Swap, lifted, and the gates in between,
-- 15,322 for the 505 letters, a fourteenth of their
-- generators -- written by reflect4_engine.py from their definitions
-- and checked once
-- (atomsM-ok).  Two runs of the same atoms spell the same generators;
-- only runs whose atoms differ are compared generator by generator.
data At : Set where
  aCCZ0 aCCZ1 aCCZ2 aSwap0 aSwap1 aSwap2 aSwap3 aiI0 aiI1 aiI2 : At
  aiI3 aiI4 aS0 aS1 aS2 aS3 aS4 aK0 aK1 aK2 : At
  aK3 aK4 aCS0 aCS1 aCS2 aCS3 : At

exA : At → Circuit 5
exA aCCZ0 = CCZ
exA aCCZ1 = CCZ ↑
exA aCCZ2 = CCZ ↑ ↑
exA aSwap0 = Swap
exA aSwap1 = Swap ↑
exA aSwap2 = Swap ↑ ↑
exA aSwap3 = Swap ↑ ↑ ↑
exA aiI0 = iI
exA aiI1 = iI ↑
exA aiI2 = iI ↑ ↑
exA aiI3 = iI ↑ ↑ ↑
exA aiI4 = iI ↑ ↑ ↑ ↑
exA aS0 = S
exA aS1 = S ↑
exA aS2 = S ↑ ↑
exA aS3 = S ↑ ↑ ↑
exA aS4 = S ↑ ↑ ↑ ↑
exA aK0 = K
exA aK1 = K ↑
exA aK2 = K ↑ ↑
exA aK3 = K ↑ ↑ ↑
exA aK4 = K ↑ ↑ ↑ ↑
exA aCS0 = CS
exA aCS1 = CS ↑
exA aCS2 = CS ↑ ↑
exA aCS3 = CS ↑ ↑ ↑

codeA : At → ℕ
codeA (aCCZ0)  = 0
codeA (aCCZ1)  = 1
codeA (aCCZ2)  = 2
codeA (aSwap0) = 3
codeA (aSwap1) = 4
codeA (aSwap2) = 5
codeA (aSwap3) = 6
codeA (aiI0)   = 7
codeA (aiI1)   = 8
codeA (aiI2)   = 9
codeA (aiI3)   = 10
codeA (aiI4)   = 11
codeA (aS0)    = 12
codeA (aS1)    = 13
codeA (aS2)    = 14
codeA (aS3)    = 15
codeA (aS4)    = 16
codeA (aK0)    = 17
codeA (aK1)    = 18
codeA (aK2)    = 19
codeA (aK3)    = 20
codeA (aK4)    = 21
codeA (aCS0)   = 22
codeA (aCS1)   = 23
codeA (aCS2)   = 24
codeA (aCS3)   = 25

tableA : List (At)
tableA =
  (aCCZ0) ∷
  (aCCZ1) ∷
  (aCCZ2) ∷
  (aSwap0) ∷
  (aSwap1) ∷
  (aSwap2) ∷
  (aSwap3) ∷
  (aiI0) ∷
  (aiI1) ∷
  (aiI2) ∷
  (aiI3) ∷
  (aiI4) ∷
  (aS0) ∷
  (aS1) ∷
  (aS2) ∷
  (aS3) ∷
  (aS4) ∷
  (aK0) ∷
  (aK1) ∷
  (aK2) ∷
  (aK3) ∷
  (aK4) ∷
  (aCS0) ∷
  (aCS1) ∷
  (aCS2) ∷
  (aCS3) ∷
  []

decodeA : ℕ → At
decodeA n = ix (aCCZ0) tableA n

decode-codeA : ∀ x → decodeA (codeA x) ≡ x
decode-codeA (aCCZ0)  = Eq.refl
decode-codeA (aCCZ1)  = Eq.refl
decode-codeA (aCCZ2)  = Eq.refl
decode-codeA (aSwap0) = Eq.refl
decode-codeA (aSwap1) = Eq.refl
decode-codeA (aSwap2) = Eq.refl
decode-codeA (aSwap3) = Eq.refl
decode-codeA (aiI0)   = Eq.refl
decode-codeA (aiI1)   = Eq.refl
decode-codeA (aiI2)   = Eq.refl
decode-codeA (aiI3)   = Eq.refl
decode-codeA (aiI4)   = Eq.refl
decode-codeA (aS0)    = Eq.refl
decode-codeA (aS1)    = Eq.refl
decode-codeA (aS2)    = Eq.refl
decode-codeA (aS3)    = Eq.refl
decode-codeA (aS4)    = Eq.refl
decode-codeA (aK0)    = Eq.refl
decode-codeA (aK1)    = Eq.refl
decode-codeA (aK2)    = Eq.refl
decode-codeA (aK3)    = Eq.refl
decode-codeA (aK4)    = Eq.refl
decode-codeA (aCS0)   = Eq.refl
decode-codeA (aCS1)   = Eq.refl
decode-codeA (aCS2)   = Eq.refl
decode-codeA (aCS3)   = Eq.refl

atomsM : Mac → List At
atomsM (ι)           = aiI0 ∷ []
atomsM (ι⁻)          = aiI0 ∷ aiI0 ∷ aiI0 ∷ []
atomsM (ι1)          = aiI1 ∷ []
atomsM (ι1⁻)         = aiI1 ∷ aiI1 ∷ aiI1 ∷ []
atomsM (ι2)          = aiI2 ∷ []
atomsM (ι2⁻)         = aiI2 ∷ aiI2 ∷ aiI2 ∷ []
atomsM (ι3)          = aiI3 ∷ []
atomsM (ι3⁻)         = aiI3 ∷ aiI3 ∷ aiI3 ∷ []
atomsM (ι4)          = aiI4 ∷ []
atomsM (ι4⁻)         = aiI4 ∷ aiI4 ∷ aiI4 ∷ []
atomsM (S0)          = aS0 ∷ []
atomsM (S0⁻)         = aS0 ∷ aS0 ∷ aS0 ∷ []
atomsM (K0)          = aK0 ∷ []
atomsM (K0⁻)         = aK0 ∷ aiI0 ∷ []
atomsM (X0)          = aK0 ∷ aS0 ∷ aS0 ∷ aK0 ∷ aiI0 ∷ []
atomsM (Z0)          = aS0 ∷ aS0 ∷ []
atomsM (S1)          = aS1 ∷ []
atomsM (S1⁻)         = aS1 ∷ aS1 ∷ aS1 ∷ []
atomsM (K1)          = aK1 ∷ []
atomsM (K1⁻)         = aK1 ∷ aiI1 ∷ []
atomsM (X1)          = aK1 ∷ aS1 ∷ aS1 ∷ aK1 ∷ aiI1 ∷ []
atomsM (Z1)          = aS1 ∷ aS1 ∷ []
atomsM (S2)          = aS2 ∷ []
atomsM (S2⁻)         = aS2 ∷ aS2 ∷ aS2 ∷ []
atomsM (K2)          = aK2 ∷ []
atomsM (K2⁻)         = aK2 ∷ aiI2 ∷ []
atomsM (X2)          = aK2 ∷ aS2 ∷ aS2 ∷ aK2 ∷ aiI2 ∷ []
atomsM (Z2)          = aS2 ∷ aS2 ∷ []
atomsM (S3)          = aS3 ∷ []
atomsM (S3⁻)         = aS3 ∷ aS3 ∷ aS3 ∷ []
atomsM (K3)          = aK3 ∷ []
atomsM (K3⁻)         = aK3 ∷ aiI3 ∷ []
atomsM (X3)          = aK3 ∷ aS3 ∷ aS3 ∷ aK3 ∷ aiI3 ∷ []
atomsM (Z3)          = aS3 ∷ aS3 ∷ []
atomsM (S4)          = aS4 ∷ []
atomsM (S4⁻)         = aS4 ∷ aS4 ∷ aS4 ∷ []
atomsM (K4)          = aK4 ∷ []
atomsM (K4⁻)         = aK4 ∷ aiI4 ∷ []
atomsM (X4)          = aK4 ∷ aS4 ∷ aS4 ∷ aK4 ∷ aiI4 ∷ []
atomsM (Z4)          = aS4 ∷ aS4 ∷ []
atomsM (CS01)        = aCS0 ∷ []
atomsM (CS01⁻)       = aCS0 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (CZ01)        = aCS0 ∷ aCS0 ∷ []
atomsM (Sw01)        = aSwap0 ∷ []
atomsM (CX01)        = aK1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aiI0 ∷ []
atomsM (CK01)        = aCS0 ∷ aK1 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aS0 ∷ aS0 ∷ aS0 ∷ aiI0 ∷ []
atomsM (CK01⁻)       = aS0 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aS0 ∷ aS0 ∷ aS0 ∷ aiI0 ∷ []
atomsM (CS02)        = aSwap1 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (CS02⁻)       = aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (CZ02)        = aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sw02)        = aSwap1 ∷ aSwap0 ∷ aSwap1 ∷ []
atomsM (CX02)        = aSwap1 ∷ aK1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aiI0 ∷ aSwap1 ∷ []
atomsM (CK02)        = aSwap1 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aS0 ∷ aS0 ∷ aS0 ∷ aiI0 ∷ aSwap1 ∷ []
atomsM (CK02⁻)       = aSwap1 ∷ aS0 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aS0 ∷ aS0 ∷ aS0 ∷ aiI0 ∷ aSwap1 ∷ []
atomsM (CS03)        = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (CS03⁻)       = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (CZ03)        = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sw03)        = aSwap2 ∷ aSwap1 ∷ aSwap0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (CX03)        = aSwap2 ∷ aSwap1 ∷ aK1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (CK03)        = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aS0 ∷ aS0 ∷ aS0 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (CK03⁻)       = aSwap2 ∷ aSwap1 ∷ aS0 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aS0 ∷ aS0 ∷ aS0 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (CS04)        = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CS04⁻)       = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CZ04)        = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sw04)        = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CX04)        = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aK1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CK04)        = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aS0 ∷ aS0 ∷ aS0 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CK04⁻)       = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aS0 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aK1 ∷ aCS0 ∷ aS0 ∷ aS0 ∷ aS0 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CX10)        = aK0 ∷ aCS0 ∷ aCS0 ∷ aK0 ∷ aiI0 ∷ []
atomsM (CK10)        = aCS0 ∷ aK0 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI0 ∷ []
atomsM (CK10⁻)       = aS1 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI0 ∷ []
atomsM (CS12)        = aCS1 ∷ []
atomsM (CS12⁻)       = aCS1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (CZ12)        = aCS1 ∷ aCS1 ∷ []
atomsM (Sw12)        = aSwap1 ∷ []
atomsM (CX12)        = aK2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aiI1 ∷ []
atomsM (CK12)        = aCS1 ∷ aK2 ∷ aCS1 ∷ aK2 ∷ aCS1 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI1 ∷ []
atomsM (CK12⁻)       = aS1 ∷ aCS1 ∷ aK2 ∷ aCS1 ∷ aK2 ∷ aCS1 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI1 ∷ []
atomsM (CS13)        = aSwap2 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (CS13⁻)       = aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (CZ13)        = aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Sw13)        = aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (CX13)        = aSwap2 ∷ aK2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aiI1 ∷ aSwap2 ∷ []
atomsM (CK13)        = aSwap2 ∷ aCS1 ∷ aK2 ∷ aCS1 ∷ aK2 ∷ aCS1 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI1 ∷ aSwap2 ∷ []
atomsM (CK13⁻)       = aSwap2 ∷ aS1 ∷ aCS1 ∷ aK2 ∷ aCS1 ∷ aK2 ∷ aCS1 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI1 ∷ aSwap2 ∷ []
atomsM (CS14)        = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CS14⁻)       = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CZ14)        = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sw14)        = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CX14)        = aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aiI1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CK14)        = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aK2 ∷ aCS1 ∷ aK2 ∷ aCS1 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CK14⁻)       = aSwap3 ∷ aSwap2 ∷ aS1 ∷ aCS1 ∷ aK2 ∷ aCS1 ∷ aK2 ∷ aCS1 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CX20)        = aSwap1 ∷ aK0 ∷ aCS0 ∷ aCS0 ∷ aK0 ∷ aiI0 ∷ aSwap1 ∷ []
atomsM (CK20)        = aSwap1 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI0 ∷ aSwap1 ∷ []
atomsM (CK20⁻)       = aSwap1 ∷ aS1 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI0 ∷ aSwap1 ∷ []
atomsM (CX21)        = aK1 ∷ aCS1 ∷ aCS1 ∷ aK1 ∷ aiI1 ∷ []
atomsM (CK21)        = aCS1 ∷ aK1 ∷ aCS1 ∷ aK1 ∷ aCS1 ∷ aS2 ∷ aS2 ∷ aS2 ∷ aiI1 ∷ []
atomsM (CK21⁻)       = aS2 ∷ aCS1 ∷ aK1 ∷ aCS1 ∷ aK1 ∷ aCS1 ∷ aS2 ∷ aS2 ∷ aS2 ∷ aiI1 ∷ []
atomsM (CS23)        = aCS2 ∷ []
atomsM (CS23⁻)       = aCS2 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (CZ23)        = aCS2 ∷ aCS2 ∷ []
atomsM (Sw23)        = aSwap2 ∷ []
atomsM (CX23)        = aK3 ∷ aCS2 ∷ aCS2 ∷ aK3 ∷ aiI2 ∷ []
atomsM (CK23)        = aCS2 ∷ aK3 ∷ aCS2 ∷ aK3 ∷ aCS2 ∷ aS2 ∷ aS2 ∷ aS2 ∷ aiI2 ∷ []
atomsM (CK23⁻)       = aS2 ∷ aCS2 ∷ aK3 ∷ aCS2 ∷ aK3 ∷ aCS2 ∷ aS2 ∷ aS2 ∷ aS2 ∷ aiI2 ∷ []
atomsM (CS24)        = aSwap3 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (CS24⁻)       = aSwap3 ∷ aCS2 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (CZ24)        = aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Sw24)        = aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CX24)        = aSwap3 ∷ aK3 ∷ aCS2 ∷ aCS2 ∷ aK3 ∷ aiI2 ∷ aSwap3 ∷ []
atomsM (CK24)        = aSwap3 ∷ aCS2 ∷ aK3 ∷ aCS2 ∷ aK3 ∷ aCS2 ∷ aS2 ∷ aS2 ∷ aS2 ∷ aiI2 ∷ aSwap3 ∷ []
atomsM (CK24⁻)       = aSwap3 ∷ aS2 ∷ aCS2 ∷ aK3 ∷ aCS2 ∷ aK3 ∷ aCS2 ∷ aS2 ∷ aS2 ∷ aS2 ∷ aiI2 ∷ aSwap3 ∷ []
atomsM (CX30)        = aSwap2 ∷ aSwap1 ∷ aK0 ∷ aCS0 ∷ aCS0 ∷ aK0 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (CK30)        = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (CK30⁻)       = aSwap2 ∷ aSwap1 ∷ aS1 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (CX31)        = aSwap2 ∷ aK1 ∷ aCS1 ∷ aCS1 ∷ aK1 ∷ aiI1 ∷ aSwap2 ∷ []
atomsM (CK31)        = aSwap2 ∷ aCS1 ∷ aK1 ∷ aCS1 ∷ aK1 ∷ aCS1 ∷ aS2 ∷ aS2 ∷ aS2 ∷ aiI1 ∷ aSwap2 ∷ []
atomsM (CK31⁻)       = aSwap2 ∷ aS2 ∷ aCS1 ∷ aK1 ∷ aCS1 ∷ aK1 ∷ aCS1 ∷ aS2 ∷ aS2 ∷ aS2 ∷ aiI1 ∷ aSwap2 ∷ []
atomsM (CX32)        = aK2 ∷ aCS2 ∷ aCS2 ∷ aK2 ∷ aiI2 ∷ []
atomsM (CK32)        = aCS2 ∷ aK2 ∷ aCS2 ∷ aK2 ∷ aCS2 ∷ aS3 ∷ aS3 ∷ aS3 ∷ aiI2 ∷ []
atomsM (CK32⁻)       = aS3 ∷ aCS2 ∷ aK2 ∷ aCS2 ∷ aK2 ∷ aCS2 ∷ aS3 ∷ aS3 ∷ aS3 ∷ aiI2 ∷ []
atomsM (CS34)        = aCS3 ∷ []
atomsM (CS34⁻)       = aCS3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (CZ34)        = aCS3 ∷ aCS3 ∷ []
atomsM (Sw34)        = aSwap3 ∷ []
atomsM (CX34)        = aK4 ∷ aCS3 ∷ aCS3 ∷ aK4 ∷ aiI3 ∷ []
atomsM (CK34)        = aCS3 ∷ aK4 ∷ aCS3 ∷ aK4 ∷ aCS3 ∷ aS3 ∷ aS3 ∷ aS3 ∷ aiI3 ∷ []
atomsM (CK34⁻)       = aS3 ∷ aCS3 ∷ aK4 ∷ aCS3 ∷ aK4 ∷ aCS3 ∷ aS3 ∷ aS3 ∷ aS3 ∷ aiI3 ∷ []
atomsM (CX40)        = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aK0 ∷ aCS0 ∷ aCS0 ∷ aK0 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CK40)        = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CK40⁻)       = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aS1 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aK0 ∷ aCS0 ∷ aS1 ∷ aS1 ∷ aS1 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CX41)        = aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCS1 ∷ aCS1 ∷ aK1 ∷ aiI1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CK41)        = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aK1 ∷ aCS1 ∷ aK1 ∷ aCS1 ∷ aS2 ∷ aS2 ∷ aS2 ∷ aiI1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CK41⁻)       = aSwap3 ∷ aSwap2 ∷ aS2 ∷ aCS1 ∷ aK1 ∷ aCS1 ∷ aK1 ∷ aCS1 ∷ aS2 ∷ aS2 ∷ aS2 ∷ aiI1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CX42)        = aSwap3 ∷ aK2 ∷ aCS2 ∷ aCS2 ∷ aK2 ∷ aiI2 ∷ aSwap3 ∷ []
atomsM (CK42)        = aSwap3 ∷ aCS2 ∷ aK2 ∷ aCS2 ∷ aK2 ∷ aCS2 ∷ aS3 ∷ aS3 ∷ aS3 ∷ aiI2 ∷ aSwap3 ∷ []
atomsM (CK42⁻)       = aSwap3 ∷ aS3 ∷ aCS2 ∷ aK2 ∷ aCS2 ∷ aK2 ∷ aCS2 ∷ aS3 ∷ aS3 ∷ aS3 ∷ aiI2 ∷ aSwap3 ∷ []
atomsM (CX43)        = aK3 ∷ aCS3 ∷ aCS3 ∷ aK3 ∷ aiI3 ∷ []
atomsM (CK43)        = aCS3 ∷ aK3 ∷ aCS3 ∷ aK3 ∷ aCS3 ∷ aS4 ∷ aS4 ∷ aS4 ∷ aiI3 ∷ []
atomsM (CK43⁻)       = aS4 ∷ aCS3 ∷ aK3 ∷ aCS3 ∷ aK3 ∷ aCS3 ∷ aS4 ∷ aS4 ∷ aS4 ∷ aiI3 ∷ []
atomsM (CCZ012)      = aCCZ0 ∷ []
atomsM (Toff012)     = aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ []
atomsM (Toff102)     = aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ []
atomsM (Toff201)     = aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ []
atomsM (CCZ013)      = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ []
atomsM (Toff013)     = aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ []
atomsM (Toff103)     = aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ []
atomsM (Toff301)     = aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ []
atomsM (CCZ014)      = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Toff014)     = aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Toff104)     = aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Toff401)     = aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (CCZ023)      = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ []
atomsM (Toff023)     = aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ []
atomsM (Toff203)     = aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ []
atomsM (Toff302)     = aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ []
atomsM (CCZ024)      = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ []
atomsM (Toff024)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ []
atomsM (Toff204)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ []
atomsM (Toff402)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ []
atomsM (CCZ034)      = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Toff034)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Toff304)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Toff403)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (CCZ123)      = aCCZ1 ∷ []
atomsM (Toff123)     = aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ []
atomsM (Toff213)     = aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ []
atomsM (Toff312)     = aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ []
atomsM (CCZ124)      = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ []
atomsM (Toff124)     = aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ []
atomsM (Toff214)     = aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ []
atomsM (Toff412)     = aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ []
atomsM (CCZ134)      = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ []
atomsM (Toff134)     = aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ []
atomsM (Toff314)     = aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ []
atomsM (Toff413)     = aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ []
atomsM (CCZ234)      = aCCZ2 ∷ []
atomsM (Toff234)     = aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ []
atomsM (Toff324)     = aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ []
atomsM (Toff423)     = aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ []
atomsM (Bx0-12)      = aCS1 ∷ aCS1 ∷ []
atomsM (Bx1-03)      = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx0-123)     = aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx0-14)      = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx1-034)     = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx0-1234)    = aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx0-13)      = aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx1-043)     = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx0-1243)    = aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx1-024)     = aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx0-1324)    = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx1-04)      = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx0-134)     = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx1-042)     = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx0-1342)    = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx1-023)     = aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx0-1423)    = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx1-032)     = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx0-1432)    = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx0-21)      = aCS1 ∷ aCS1 ∷ []
atomsM (Bx2-03)      = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx0-213)     = aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx0-24)      = aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx2-034)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx0-2134)    = aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx2-04)      = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx0-214)     = aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx0-23)      = aCS2 ∷ aCS2 ∷ []
atomsM (Bx2-043)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx0-2143)    = aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx2-01)      = aCS0 ∷ aCS0 ∷ []
atomsM (Bx0-231)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx2-014)     = aCCZ0 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx0-2314)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ0 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ0 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx0-234)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx2-041)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx0-2341)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx0-241)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx2-013)     = aCCZ0 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCS2 ∷ aCS2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCCZ0 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx0-2413)    = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ0 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCS2 ∷ aCS2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCCZ0 ∷ aCS2 ∷ aCS2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ0 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCS2 ∷ aCS2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCCZ0 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx0-243)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx2-031)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx0-2431)    = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx0-31)      = aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx3-02)      = aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx0-312)     = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx0-34)      = aCS3 ∷ aCS3 ∷ []
atomsM (Bx3-024)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx0-3124)    = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx3-04)      = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx0-314)     = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx0-32)      = aCS2 ∷ aCS2 ∷ []
atomsM (Bx3-042)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx0-3142)    = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx3-01)      = aCS0 ∷ aCS0 ∷ []
atomsM (Bx0-321)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx3-014)     = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCS3 ∷ aCS3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx0-3214)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCS3 ∷ aCS3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCS3 ∷ aCS3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx0-324)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-041)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx0-3241)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx0-341)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx3-012)     = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx0-3412)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx0-342)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx3-021)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx0-3421)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx0-41)      = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx4-02)      = aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx0-412)     = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx0-43)      = aCS3 ∷ aCS3 ∷ []
atomsM (Bx4-023)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx0-4123)    = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx4-03)      = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx0-413)     = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx0-42)      = aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx4-032)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx0-4132)    = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx4-01)      = aCS0 ∷ aCS0 ∷ []
atomsM (Bx0-421)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx4-013)     = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx0-4213)    = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx0-423)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx4-031)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx0-4231)    = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx0-431)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx4-012)     = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx0-4312)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx4-021)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx0-4321)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx1-0234)    = aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx1-0423)    = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx1-20)      = aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx2-14)      = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx1-204)     = aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx2-10)      = aCS0 ∷ aCS0 ∷ []
atomsM (Bx1-230)     = aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx1-234)     = aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx1-240)     = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx2-130)     = aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx1-2430)    = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx3-12)      = aCS1 ∷ aCS1 ∷ []
atomsM (Bx1-302)     = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx3-14)      = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx1-304)     = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-10)      = aCS0 ∷ aCS0 ∷ []
atomsM (Bx1-320)     = aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx1-324)     = aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx1-340)     = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx1-342)     = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx4-12)      = aCS1 ∷ aCS1 ∷ []
atomsM (Bx1-402)     = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx4-13)      = aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx1-403)     = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx4-10)      = aCS0 ∷ aCS0 ∷ []
atomsM (Bx1-420)     = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx1-43)      = aCS3 ∷ aCS3 ∷ []
atomsM (Bx4-103)     = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx1-4203)    = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx1-423)     = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx1-430)     = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx2-0134)    = aCCZ0 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCCZ0 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx2-0143)    = aCCZ0 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCCZ0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx2-0314)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx2-0341)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx2-0413)    = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx2-0431)    = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx2-1034)    = aCCZ0 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aCCZ0 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx2-1304)    = aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx2-1340)    = aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx2-1430)    = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx2-30)      = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx3-21)      = aCS1 ∷ aCS1 ∷ []
atomsM (Bx2-301)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx2-34)      = aCS3 ∷ aCS3 ∷ []
atomsM (Bx3-214)     = aCCZ1 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCS3 ∷ aCS3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCCZ1 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx2-3014)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ1 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCS3 ∷ aCS3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCCZ1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ1 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCS3 ∷ aCS3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCCZ1 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx3-24)      = aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx2-304)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx2-31)      = aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx3-241)     = aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx2-3041)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx3-20)      = aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx2-310)     = aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx3-204)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx2-3104)    = aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx2-314)     = aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx3-240)     = aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx2-3140)    = aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx2-340)     = aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx3-201)     = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx2-3401)    = aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx2-341)     = aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx3-210)     = aCCZ1 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCCZ1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx2-3410)    = aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ1 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCCZ1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aCCZ1 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCCZ1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx2-40)      = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx4-21)      = aCS1 ∷ aCS1 ∷ []
atomsM (Bx2-401)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx2-43)      = aCS3 ∷ aCS3 ∷ []
atomsM (Bx4-213)     = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx2-4013)    = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx4-23)      = aCS2 ∷ aCS2 ∷ []
atomsM (Bx2-403)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx2-41)      = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx4-231)     = aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx2-4031)    = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx4-20)      = aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx2-410)     = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx4-203)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx2-4103)    = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Bx4-230)     = aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx2-4130)    = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx2-430)     = aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx4-201)     = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx2-4301)    = aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx2-431)     = aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx3-0124)    = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-0142)    = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx3-0214)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-0241)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx3-0412)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx3-0421)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx3-1024)    = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-1042)    = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx3-1204)    = aCCZ1 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCCZ1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-1240)    = aCCZ1 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCCZ1 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx3-1402)    = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx3-1420)    = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx3-2014)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx3-2041)    = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx3-2104)    = aCCZ1 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCCZ1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx3-2140)    = aCCZ1 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCCZ1 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx3-2401)    = aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx3-2410)    = aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx3-40)      = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-42)      = aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx4-312)     = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx3-4012)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx4-32)      = aCS2 ∷ aCS2 ∷ []
atomsM (Bx3-402)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx3-41)      = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx4-321)     = aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-4021)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx4-30)      = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx3-410)     = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx4-302)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx3-4102)    = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Bx3-412)     = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx4-320)     = aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-4120)    = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-420)     = aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx4-301)     = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-4201)    = aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx4-31)      = aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx3-421)     = aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx4-310)     = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx3-4210)    = aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Bx4-0123)    = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx4-0213)    = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx4-0231)    = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx4-0312)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx4-0321)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx4-1023)    = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx4-1203)    = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx4-1230)    = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx4-1302)    = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx4-1320)    = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Bx4-2031)    = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx4-2103)    = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx4-2130)    = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx4-2301)    = aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Bx4-2310)    = aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Bx4-3012)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx4-3021)    = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Bx4-3102)    = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS2 ∷ aCS2 ∷ []
atomsM (Bx4-3120)    = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx4-3210)    = aCCZ2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK4 ∷ aCCZ2 ∷ aK4 ∷ aiI2 ∷ aCCZ2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx⁻2-03)     = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Bx⁻0-213)    = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ []
atomsM (Bx⁻2-0413)   = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ []
atomsM (Sb0-1-2-3)   = aCS1 ∷ []
atomsM (Sb0-1-3-2)   = aSwap2 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Sb⁻0-1-3-2)  = aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Sb0-1-42-3)  = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ0 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aCS1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Sb⁻0-1-2-3)  = aCS1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Sb0-1-43-2)  = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCS1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Sb0-2-1-3)   = aCS1 ∷ []
atomsM (Sb⁻0-2-1-3)  = aCS1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Sb0-2-43-1)  = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Sb0-3-1-2)   = aSwap2 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Sb⁻0-3-1-2)  = aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Sb0-3-42-1)  = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Sb0-4-1-2)   = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb0-4-2-1)   = aSwap3 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Sb0-4-3-1)   = aCS3 ∷ []
atomsM (Sb⁻0-4-3-1)  = aCS3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Sb0-4-21-3)  = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCS3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aCS3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Sb⁻0-4-2-1)  = aSwap3 ∷ aCS2 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Sb0-4-31-2)  = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aCS2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Sb⁻0-4-1-2)  = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb0-4-32-1)  = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb1-0-3-2)   = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb⁻1-0-3-2)  = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb1-0-42-3)  = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ2 ∷ aK3 ∷ aiI2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb1-2-0-3)   = aSwap1 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb⁻1-2-0-3)  = aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb1-2-43-0)  = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCCZ1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aCCZ1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb1-4-3-0)   = aCS3 ∷ []
atomsM (Sb⁻1-4-3-0)  = aCS3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Sb1-4-20-3)  = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Sb2-0-3-1)   = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb⁻2-0-3-1)  = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb2-0-41-3)  = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb2-1-0-3)   = aCS0 ∷ []
atomsM (Sb⁻2-1-0-3)  = aCS0 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Sb2-1-43-0)  = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Sb2-4-3-1)   = aCS3 ∷ []
atomsM (Sb⁻2-4-3-1)  = aCS3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Sb2-4-01-3)  = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS3 ∷ aCS3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCS3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCS3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Sb2-4-3-0)   = aCS3 ∷ []
atomsM (Sb⁻2-4-3-0)  = aCS3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Sb2-4-10-3)  = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS3 ∷ aCS3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCS3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCS3 ∷ aCS3 ∷ aCS3 ∷ []
atomsM (Sb3-0-4-2)   = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb⁻3-0-4-2)  = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb3-0-12-4)  = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb3-0-2-1)   = aSwap1 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb3-0-4-1)   = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb⁻3-0-4-1)  = aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb3-0-21-4)  = aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb⁻3-0-2-1)  = aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb3-0-41-2)  = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb3-1-0-2)   = aCS0 ∷ []
atomsM (Sb3-1-4-2)   = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb⁻3-1-4-2)  = aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb3-1-02-4)  = aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ []
atomsM (Sb⁻3-1-0-2)  = aCS0 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Sb3-1-42-0)  = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ1 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCS0 ∷ aCS0 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aCCZ1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Sb3-4-2-1)   = aSwap3 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Sb⁻3-4-2-1)  = aSwap3 ∷ aCS2 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Sb3-4-01-2)  = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap3 ∷ aCS2 ∷ aSwap3 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap3 ∷ aCS2 ∷ aCS2 ∷ aCS2 ∷ aSwap3 ∷ []
atomsM (Sb4-0-3-2)   = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb⁻4-0-3-2)  = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb4-0-12-3)  = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb4-0-2-1)   = aSwap1 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb4-0-3-1)   = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb⁻4-0-3-1)  = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb4-0-21-3)  = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ []
atomsM (Sb⁻4-0-2-1)  = aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb4-0-31-2)  = aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb4-1-0-2)   = aCS0 ∷ []
atomsM (Sb4-1-0-3)   = aCS0 ∷ []
atomsM (Sb4-1-3-2)   = aSwap2 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Sb⁻4-1-3-2)  = aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Sb4-1-02-3)  = aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ []
atomsM (Sb⁻4-1-0-3)  = aCS0 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Sb4-1-23-0)  = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Sb⁻4-1-0-2)  = aCS0 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Sb4-1-32-0)  = aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aSwap2 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aSwap3 ∷ aK1 ∷ aCCZ1 ∷ aK1 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ []
atomsM (Sb4-2-0-3)   = aSwap1 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb4-2-1-3)   = aCS1 ∷ []
atomsM (Sb⁻4-2-1-3)  = aCS1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Sb4-2-03-1)  = aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aCS1 ∷ aCS1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK2 ∷ aCCZ0 ∷ aK2 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCS1 ∷ aCS1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aCS1 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aCS1 ∷ aCS1 ∷ aCS1 ∷ []
atomsM (Sb⁻4-2-0-3)  = aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb4-2-13-0)  = aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap3 ∷ aK3 ∷ aCCZ1 ∷ aK3 ∷ aiI1 ∷ aSwap3 ∷ aSwap3 ∷ aCCZ1 ∷ aSwap3 ∷ aCCZ2 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aK2 ∷ aCCZ2 ∷ aK2 ∷ aiI2 ∷ aCCZ2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ []
atomsM (Sb⁻2-0-41-3) = aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aSwap2 ∷ aSwap3 ∷ aK2 ∷ aCCZ1 ∷ aK2 ∷ aiI1 ∷ aSwap3 ∷ aSwap2 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aCCZ0 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aSwap2 ∷ aSwap1 ∷ aCS0 ∷ aCS0 ∷ aSwap1 ∷ aSwap2 ∷ aK0 ∷ aCCZ0 ∷ aK0 ∷ aiI0 ∷ aCCZ0 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aK1 ∷ aCCZ0 ∷ aK1 ∷ aiI0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ aSwap1 ∷ aSwap3 ∷ aSwap2 ∷ aCCZ0 ∷ aSwap2 ∷ aSwap3 ∷ aSwap1 ∷ []

flatA : List At → List (Gen 5)
flatA []       = []
flatA (a ∷ as) = to-list (exA a) ++ flatA as

atomsM-ok : ∀ x → flat (x ∷ []) ≡ flatA (atomsM x)
atomsM-ok (ι)           = Eq.refl
atomsM-ok (ι⁻)          = Eq.refl
atomsM-ok (ι1)          = Eq.refl
atomsM-ok (ι1⁻)         = Eq.refl
atomsM-ok (ι2)          = Eq.refl
atomsM-ok (ι2⁻)         = Eq.refl
atomsM-ok (ι3)          = Eq.refl
atomsM-ok (ι3⁻)         = Eq.refl
atomsM-ok (ι4)          = Eq.refl
atomsM-ok (ι4⁻)         = Eq.refl
atomsM-ok (S0)          = Eq.refl
atomsM-ok (S0⁻)         = Eq.refl
atomsM-ok (K0)          = Eq.refl
atomsM-ok (K0⁻)         = Eq.refl
atomsM-ok (X0)          = Eq.refl
atomsM-ok (Z0)          = Eq.refl
atomsM-ok (S1)          = Eq.refl
atomsM-ok (S1⁻)         = Eq.refl
atomsM-ok (K1)          = Eq.refl
atomsM-ok (K1⁻)         = Eq.refl
atomsM-ok (X1)          = Eq.refl
atomsM-ok (Z1)          = Eq.refl
atomsM-ok (S2)          = Eq.refl
atomsM-ok (S2⁻)         = Eq.refl
atomsM-ok (K2)          = Eq.refl
atomsM-ok (K2⁻)         = Eq.refl
atomsM-ok (X2)          = Eq.refl
atomsM-ok (Z2)          = Eq.refl
atomsM-ok (S3)          = Eq.refl
atomsM-ok (S3⁻)         = Eq.refl
atomsM-ok (K3)          = Eq.refl
atomsM-ok (K3⁻)         = Eq.refl
atomsM-ok (X3)          = Eq.refl
atomsM-ok (Z3)          = Eq.refl
atomsM-ok (S4)          = Eq.refl
atomsM-ok (S4⁻)         = Eq.refl
atomsM-ok (K4)          = Eq.refl
atomsM-ok (K4⁻)         = Eq.refl
atomsM-ok (X4)          = Eq.refl
atomsM-ok (Z4)          = Eq.refl
atomsM-ok (CS01)        = Eq.refl
atomsM-ok (CS01⁻)       = Eq.refl
atomsM-ok (CZ01)        = Eq.refl
atomsM-ok (Sw01)        = Eq.refl
atomsM-ok (CX01)        = Eq.refl
atomsM-ok (CK01)        = Eq.refl
atomsM-ok (CK01⁻)       = Eq.refl
atomsM-ok (CS02)        = Eq.refl
atomsM-ok (CS02⁻)       = Eq.refl
atomsM-ok (CZ02)        = Eq.refl
atomsM-ok (Sw02)        = Eq.refl
atomsM-ok (CX02)        = Eq.refl
atomsM-ok (CK02)        = Eq.refl
atomsM-ok (CK02⁻)       = Eq.refl
atomsM-ok (CS03)        = Eq.refl
atomsM-ok (CS03⁻)       = Eq.refl
atomsM-ok (CZ03)        = Eq.refl
atomsM-ok (Sw03)        = Eq.refl
atomsM-ok (CX03)        = Eq.refl
atomsM-ok (CK03)        = Eq.refl
atomsM-ok (CK03⁻)       = Eq.refl
atomsM-ok (CS04)        = Eq.refl
atomsM-ok (CS04⁻)       = Eq.refl
atomsM-ok (CZ04)        = Eq.refl
atomsM-ok (Sw04)        = Eq.refl
atomsM-ok (CX04)        = Eq.refl
atomsM-ok (CK04)        = Eq.refl
atomsM-ok (CK04⁻)       = Eq.refl
atomsM-ok (CX10)        = Eq.refl
atomsM-ok (CK10)        = Eq.refl
atomsM-ok (CK10⁻)       = Eq.refl
atomsM-ok (CS12)        = Eq.refl
atomsM-ok (CS12⁻)       = Eq.refl
atomsM-ok (CZ12)        = Eq.refl
atomsM-ok (Sw12)        = Eq.refl
atomsM-ok (CX12)        = Eq.refl
atomsM-ok (CK12)        = Eq.refl
atomsM-ok (CK12⁻)       = Eq.refl
atomsM-ok (CS13)        = Eq.refl
atomsM-ok (CS13⁻)       = Eq.refl
atomsM-ok (CZ13)        = Eq.refl
atomsM-ok (Sw13)        = Eq.refl
atomsM-ok (CX13)        = Eq.refl
atomsM-ok (CK13)        = Eq.refl
atomsM-ok (CK13⁻)       = Eq.refl
atomsM-ok (CS14)        = Eq.refl
atomsM-ok (CS14⁻)       = Eq.refl
atomsM-ok (CZ14)        = Eq.refl
atomsM-ok (Sw14)        = Eq.refl
atomsM-ok (CX14)        = Eq.refl
atomsM-ok (CK14)        = Eq.refl
atomsM-ok (CK14⁻)       = Eq.refl
atomsM-ok (CX20)        = Eq.refl
atomsM-ok (CK20)        = Eq.refl
atomsM-ok (CK20⁻)       = Eq.refl
atomsM-ok (CX21)        = Eq.refl
atomsM-ok (CK21)        = Eq.refl
atomsM-ok (CK21⁻)       = Eq.refl
atomsM-ok (CS23)        = Eq.refl
atomsM-ok (CS23⁻)       = Eq.refl
atomsM-ok (CZ23)        = Eq.refl
atomsM-ok (Sw23)        = Eq.refl
atomsM-ok (CX23)        = Eq.refl
atomsM-ok (CK23)        = Eq.refl
atomsM-ok (CK23⁻)       = Eq.refl
atomsM-ok (CS24)        = Eq.refl
atomsM-ok (CS24⁻)       = Eq.refl
atomsM-ok (CZ24)        = Eq.refl
atomsM-ok (Sw24)        = Eq.refl
atomsM-ok (CX24)        = Eq.refl
atomsM-ok (CK24)        = Eq.refl
atomsM-ok (CK24⁻)       = Eq.refl
atomsM-ok (CX30)        = Eq.refl
atomsM-ok (CK30)        = Eq.refl
atomsM-ok (CK30⁻)       = Eq.refl
atomsM-ok (CX31)        = Eq.refl
atomsM-ok (CK31)        = Eq.refl
atomsM-ok (CK31⁻)       = Eq.refl
atomsM-ok (CX32)        = Eq.refl
atomsM-ok (CK32)        = Eq.refl
atomsM-ok (CK32⁻)       = Eq.refl
atomsM-ok (CS34)        = Eq.refl
atomsM-ok (CS34⁻)       = Eq.refl
atomsM-ok (CZ34)        = Eq.refl
atomsM-ok (Sw34)        = Eq.refl
atomsM-ok (CX34)        = Eq.refl
atomsM-ok (CK34)        = Eq.refl
atomsM-ok (CK34⁻)       = Eq.refl
atomsM-ok (CX40)        = Eq.refl
atomsM-ok (CK40)        = Eq.refl
atomsM-ok (CK40⁻)       = Eq.refl
atomsM-ok (CX41)        = Eq.refl
atomsM-ok (CK41)        = Eq.refl
atomsM-ok (CK41⁻)       = Eq.refl
atomsM-ok (CX42)        = Eq.refl
atomsM-ok (CK42)        = Eq.refl
atomsM-ok (CK42⁻)       = Eq.refl
atomsM-ok (CX43)        = Eq.refl
atomsM-ok (CK43)        = Eq.refl
atomsM-ok (CK43⁻)       = Eq.refl
atomsM-ok (CCZ012)      = Eq.refl
atomsM-ok (Toff012)     = Eq.refl
atomsM-ok (Toff102)     = Eq.refl
atomsM-ok (Toff201)     = Eq.refl
atomsM-ok (CCZ013)      = Eq.refl
atomsM-ok (Toff013)     = Eq.refl
atomsM-ok (Toff103)     = Eq.refl
atomsM-ok (Toff301)     = Eq.refl
atomsM-ok (CCZ014)      = Eq.refl
atomsM-ok (Toff014)     = Eq.refl
atomsM-ok (Toff104)     = Eq.refl
atomsM-ok (Toff401)     = Eq.refl
atomsM-ok (CCZ023)      = Eq.refl
atomsM-ok (Toff023)     = Eq.refl
atomsM-ok (Toff203)     = Eq.refl
atomsM-ok (Toff302)     = Eq.refl
atomsM-ok (CCZ024)      = Eq.refl
atomsM-ok (Toff024)     = Eq.refl
atomsM-ok (Toff204)     = Eq.refl
atomsM-ok (Toff402)     = Eq.refl
atomsM-ok (CCZ034)      = Eq.refl
atomsM-ok (Toff034)     = Eq.refl
atomsM-ok (Toff304)     = Eq.refl
atomsM-ok (Toff403)     = Eq.refl
atomsM-ok (CCZ123)      = Eq.refl
atomsM-ok (Toff123)     = Eq.refl
atomsM-ok (Toff213)     = Eq.refl
atomsM-ok (Toff312)     = Eq.refl
atomsM-ok (CCZ124)      = Eq.refl
atomsM-ok (Toff124)     = Eq.refl
atomsM-ok (Toff214)     = Eq.refl
atomsM-ok (Toff412)     = Eq.refl
atomsM-ok (CCZ134)      = Eq.refl
atomsM-ok (Toff134)     = Eq.refl
atomsM-ok (Toff314)     = Eq.refl
atomsM-ok (Toff413)     = Eq.refl
atomsM-ok (CCZ234)      = Eq.refl
atomsM-ok (Toff234)     = Eq.refl
atomsM-ok (Toff324)     = Eq.refl
atomsM-ok (Toff423)     = Eq.refl
atomsM-ok (Bx0-12)      = Eq.refl
atomsM-ok (Bx1-03)      = Eq.refl
atomsM-ok (Bx0-123)     = Eq.refl
atomsM-ok (Bx0-14)      = Eq.refl
atomsM-ok (Bx1-034)     = Eq.refl
atomsM-ok (Bx0-1234)    = Eq.refl
atomsM-ok (Bx0-13)      = Eq.refl
atomsM-ok (Bx1-043)     = Eq.refl
atomsM-ok (Bx0-1243)    = Eq.refl
atomsM-ok (Bx1-024)     = Eq.refl
atomsM-ok (Bx0-1324)    = Eq.refl
atomsM-ok (Bx1-04)      = Eq.refl
atomsM-ok (Bx0-134)     = Eq.refl
atomsM-ok (Bx1-042)     = Eq.refl
atomsM-ok (Bx0-1342)    = Eq.refl
atomsM-ok (Bx1-023)     = Eq.refl
atomsM-ok (Bx0-1423)    = Eq.refl
atomsM-ok (Bx1-032)     = Eq.refl
atomsM-ok (Bx0-1432)    = Eq.refl
atomsM-ok (Bx0-21)      = Eq.refl
atomsM-ok (Bx2-03)      = Eq.refl
atomsM-ok (Bx0-213)     = Eq.refl
atomsM-ok (Bx0-24)      = Eq.refl
atomsM-ok (Bx2-034)     = Eq.refl
atomsM-ok (Bx0-2134)    = Eq.refl
atomsM-ok (Bx2-04)      = Eq.refl
atomsM-ok (Bx0-214)     = Eq.refl
atomsM-ok (Bx0-23)      = Eq.refl
atomsM-ok (Bx2-043)     = Eq.refl
atomsM-ok (Bx0-2143)    = Eq.refl
atomsM-ok (Bx2-01)      = Eq.refl
atomsM-ok (Bx0-231)     = Eq.refl
atomsM-ok (Bx2-014)     = Eq.refl
atomsM-ok (Bx0-2314)    = Eq.refl
atomsM-ok (Bx0-234)     = Eq.refl
atomsM-ok (Bx2-041)     = Eq.refl
atomsM-ok (Bx0-2341)    = Eq.refl
atomsM-ok (Bx0-241)     = Eq.refl
atomsM-ok (Bx2-013)     = Eq.refl
atomsM-ok (Bx0-2413)    = Eq.refl
atomsM-ok (Bx0-243)     = Eq.refl
atomsM-ok (Bx2-031)     = Eq.refl
atomsM-ok (Bx0-2431)    = Eq.refl
atomsM-ok (Bx0-31)      = Eq.refl
atomsM-ok (Bx3-02)      = Eq.refl
atomsM-ok (Bx0-312)     = Eq.refl
atomsM-ok (Bx0-34)      = Eq.refl
atomsM-ok (Bx3-024)     = Eq.refl
atomsM-ok (Bx0-3124)    = Eq.refl
atomsM-ok (Bx3-04)      = Eq.refl
atomsM-ok (Bx0-314)     = Eq.refl
atomsM-ok (Bx0-32)      = Eq.refl
atomsM-ok (Bx3-042)     = Eq.refl
atomsM-ok (Bx0-3142)    = Eq.refl
atomsM-ok (Bx3-01)      = Eq.refl
atomsM-ok (Bx0-321)     = Eq.refl
atomsM-ok (Bx3-014)     = Eq.refl
atomsM-ok (Bx0-3214)    = Eq.refl
atomsM-ok (Bx0-324)     = Eq.refl
atomsM-ok (Bx3-041)     = Eq.refl
atomsM-ok (Bx0-3241)    = Eq.refl
atomsM-ok (Bx0-341)     = Eq.refl
atomsM-ok (Bx3-012)     = Eq.refl
atomsM-ok (Bx0-3412)    = Eq.refl
atomsM-ok (Bx0-342)     = Eq.refl
atomsM-ok (Bx3-021)     = Eq.refl
atomsM-ok (Bx0-3421)    = Eq.refl
atomsM-ok (Bx0-41)      = Eq.refl
atomsM-ok (Bx4-02)      = Eq.refl
atomsM-ok (Bx0-412)     = Eq.refl
atomsM-ok (Bx0-43)      = Eq.refl
atomsM-ok (Bx4-023)     = Eq.refl
atomsM-ok (Bx0-4123)    = Eq.refl
atomsM-ok (Bx4-03)      = Eq.refl
atomsM-ok (Bx0-413)     = Eq.refl
atomsM-ok (Bx0-42)      = Eq.refl
atomsM-ok (Bx4-032)     = Eq.refl
atomsM-ok (Bx0-4132)    = Eq.refl
atomsM-ok (Bx4-01)      = Eq.refl
atomsM-ok (Bx0-421)     = Eq.refl
atomsM-ok (Bx4-013)     = Eq.refl
atomsM-ok (Bx0-4213)    = Eq.refl
atomsM-ok (Bx0-423)     = Eq.refl
atomsM-ok (Bx4-031)     = Eq.refl
atomsM-ok (Bx0-4231)    = Eq.refl
atomsM-ok (Bx0-431)     = Eq.refl
atomsM-ok (Bx4-012)     = Eq.refl
atomsM-ok (Bx0-4312)    = Eq.refl
atomsM-ok (Bx4-021)     = Eq.refl
atomsM-ok (Bx0-4321)    = Eq.refl
atomsM-ok (Bx1-0234)    = Eq.refl
atomsM-ok (Bx1-0423)    = Eq.refl
atomsM-ok (Bx1-20)      = Eq.refl
atomsM-ok (Bx2-14)      = Eq.refl
atomsM-ok (Bx1-204)     = Eq.refl
atomsM-ok (Bx2-10)      = Eq.refl
atomsM-ok (Bx1-230)     = Eq.refl
atomsM-ok (Bx1-234)     = Eq.refl
atomsM-ok (Bx1-240)     = Eq.refl
atomsM-ok (Bx2-130)     = Eq.refl
atomsM-ok (Bx1-2430)    = Eq.refl
atomsM-ok (Bx3-12)      = Eq.refl
atomsM-ok (Bx1-302)     = Eq.refl
atomsM-ok (Bx3-14)      = Eq.refl
atomsM-ok (Bx1-304)     = Eq.refl
atomsM-ok (Bx3-10)      = Eq.refl
atomsM-ok (Bx1-320)     = Eq.refl
atomsM-ok (Bx1-324)     = Eq.refl
atomsM-ok (Bx1-340)     = Eq.refl
atomsM-ok (Bx1-342)     = Eq.refl
atomsM-ok (Bx4-12)      = Eq.refl
atomsM-ok (Bx1-402)     = Eq.refl
atomsM-ok (Bx4-13)      = Eq.refl
atomsM-ok (Bx1-403)     = Eq.refl
atomsM-ok (Bx4-10)      = Eq.refl
atomsM-ok (Bx1-420)     = Eq.refl
atomsM-ok (Bx1-43)      = Eq.refl
atomsM-ok (Bx4-103)     = Eq.refl
atomsM-ok (Bx1-4203)    = Eq.refl
atomsM-ok (Bx1-423)     = Eq.refl
atomsM-ok (Bx1-430)     = Eq.refl
atomsM-ok (Bx2-0134)    = Eq.refl
atomsM-ok (Bx2-0143)    = Eq.refl
atomsM-ok (Bx2-0314)    = Eq.refl
atomsM-ok (Bx2-0341)    = Eq.refl
atomsM-ok (Bx2-0413)    = Eq.refl
atomsM-ok (Bx2-0431)    = Eq.refl
atomsM-ok (Bx2-1034)    = Eq.refl
atomsM-ok (Bx2-1304)    = Eq.refl
atomsM-ok (Bx2-1340)    = Eq.refl
atomsM-ok (Bx2-1430)    = Eq.refl
atomsM-ok (Bx2-30)      = Eq.refl
atomsM-ok (Bx3-21)      = Eq.refl
atomsM-ok (Bx2-301)     = Eq.refl
atomsM-ok (Bx2-34)      = Eq.refl
atomsM-ok (Bx3-214)     = Eq.refl
atomsM-ok (Bx2-3014)    = Eq.refl
atomsM-ok (Bx3-24)      = Eq.refl
atomsM-ok (Bx2-304)     = Eq.refl
atomsM-ok (Bx2-31)      = Eq.refl
atomsM-ok (Bx3-241)     = Eq.refl
atomsM-ok (Bx2-3041)    = Eq.refl
atomsM-ok (Bx3-20)      = Eq.refl
atomsM-ok (Bx2-310)     = Eq.refl
atomsM-ok (Bx3-204)     = Eq.refl
atomsM-ok (Bx2-3104)    = Eq.refl
atomsM-ok (Bx2-314)     = Eq.refl
atomsM-ok (Bx3-240)     = Eq.refl
atomsM-ok (Bx2-3140)    = Eq.refl
atomsM-ok (Bx2-340)     = Eq.refl
atomsM-ok (Bx3-201)     = Eq.refl
atomsM-ok (Bx2-3401)    = Eq.refl
atomsM-ok (Bx2-341)     = Eq.refl
atomsM-ok (Bx3-210)     = Eq.refl
atomsM-ok (Bx2-3410)    = Eq.refl
atomsM-ok (Bx2-40)      = Eq.refl
atomsM-ok (Bx4-21)      = Eq.refl
atomsM-ok (Bx2-401)     = Eq.refl
atomsM-ok (Bx2-43)      = Eq.refl
atomsM-ok (Bx4-213)     = Eq.refl
atomsM-ok (Bx2-4013)    = Eq.refl
atomsM-ok (Bx4-23)      = Eq.refl
atomsM-ok (Bx2-403)     = Eq.refl
atomsM-ok (Bx2-41)      = Eq.refl
atomsM-ok (Bx4-231)     = Eq.refl
atomsM-ok (Bx2-4031)    = Eq.refl
atomsM-ok (Bx4-20)      = Eq.refl
atomsM-ok (Bx2-410)     = Eq.refl
atomsM-ok (Bx4-203)     = Eq.refl
atomsM-ok (Bx2-4103)    = Eq.refl
atomsM-ok (Bx4-230)     = Eq.refl
atomsM-ok (Bx2-4130)    = Eq.refl
atomsM-ok (Bx2-430)     = Eq.refl
atomsM-ok (Bx4-201)     = Eq.refl
atomsM-ok (Bx2-4301)    = Eq.refl
atomsM-ok (Bx2-431)     = Eq.refl
atomsM-ok (Bx3-0124)    = Eq.refl
atomsM-ok (Bx3-0142)    = Eq.refl
atomsM-ok (Bx3-0214)    = Eq.refl
atomsM-ok (Bx3-0241)    = Eq.refl
atomsM-ok (Bx3-0412)    = Eq.refl
atomsM-ok (Bx3-0421)    = Eq.refl
atomsM-ok (Bx3-1024)    = Eq.refl
atomsM-ok (Bx3-1042)    = Eq.refl
atomsM-ok (Bx3-1204)    = Eq.refl
atomsM-ok (Bx3-1240)    = Eq.refl
atomsM-ok (Bx3-1402)    = Eq.refl
atomsM-ok (Bx3-1420)    = Eq.refl
atomsM-ok (Bx3-2014)    = Eq.refl
atomsM-ok (Bx3-2041)    = Eq.refl
atomsM-ok (Bx3-2104)    = Eq.refl
atomsM-ok (Bx3-2140)    = Eq.refl
atomsM-ok (Bx3-2401)    = Eq.refl
atomsM-ok (Bx3-2410)    = Eq.refl
atomsM-ok (Bx3-40)      = Eq.refl
atomsM-ok (Bx3-42)      = Eq.refl
atomsM-ok (Bx4-312)     = Eq.refl
atomsM-ok (Bx3-4012)    = Eq.refl
atomsM-ok (Bx4-32)      = Eq.refl
atomsM-ok (Bx3-402)     = Eq.refl
atomsM-ok (Bx3-41)      = Eq.refl
atomsM-ok (Bx4-321)     = Eq.refl
atomsM-ok (Bx3-4021)    = Eq.refl
atomsM-ok (Bx4-30)      = Eq.refl
atomsM-ok (Bx3-410)     = Eq.refl
atomsM-ok (Bx4-302)     = Eq.refl
atomsM-ok (Bx3-4102)    = Eq.refl
atomsM-ok (Bx3-412)     = Eq.refl
atomsM-ok (Bx4-320)     = Eq.refl
atomsM-ok (Bx3-4120)    = Eq.refl
atomsM-ok (Bx3-420)     = Eq.refl
atomsM-ok (Bx4-301)     = Eq.refl
atomsM-ok (Bx3-4201)    = Eq.refl
atomsM-ok (Bx4-31)      = Eq.refl
atomsM-ok (Bx3-421)     = Eq.refl
atomsM-ok (Bx4-310)     = Eq.refl
atomsM-ok (Bx3-4210)    = Eq.refl
atomsM-ok (Bx4-0123)    = Eq.refl
atomsM-ok (Bx4-0213)    = Eq.refl
atomsM-ok (Bx4-0231)    = Eq.refl
atomsM-ok (Bx4-0312)    = Eq.refl
atomsM-ok (Bx4-0321)    = Eq.refl
atomsM-ok (Bx4-1023)    = Eq.refl
atomsM-ok (Bx4-1203)    = Eq.refl
atomsM-ok (Bx4-1230)    = Eq.refl
atomsM-ok (Bx4-1302)    = Eq.refl
atomsM-ok (Bx4-1320)    = Eq.refl
atomsM-ok (Bx4-2031)    = Eq.refl
atomsM-ok (Bx4-2103)    = Eq.refl
atomsM-ok (Bx4-2130)    = Eq.refl
atomsM-ok (Bx4-2301)    = Eq.refl
atomsM-ok (Bx4-2310)    = Eq.refl
atomsM-ok (Bx4-3012)    = Eq.refl
atomsM-ok (Bx4-3021)    = Eq.refl
atomsM-ok (Bx4-3102)    = Eq.refl
atomsM-ok (Bx4-3120)    = Eq.refl
atomsM-ok (Bx4-3210)    = Eq.refl
atomsM-ok (Bx⁻2-03)     = Eq.refl
atomsM-ok (Bx⁻0-213)    = Eq.refl
atomsM-ok (Bx⁻2-0413)   = Eq.refl
atomsM-ok (Sb0-1-2-3)   = Eq.refl
atomsM-ok (Sb0-1-3-2)   = Eq.refl
atomsM-ok (Sb⁻0-1-3-2)  = Eq.refl
atomsM-ok (Sb0-1-42-3)  = Eq.refl
atomsM-ok (Sb⁻0-1-2-3)  = Eq.refl
atomsM-ok (Sb0-1-43-2)  = Eq.refl
atomsM-ok (Sb0-2-1-3)   = Eq.refl
atomsM-ok (Sb⁻0-2-1-3)  = Eq.refl
atomsM-ok (Sb0-2-43-1)  = Eq.refl
atomsM-ok (Sb0-3-1-2)   = Eq.refl
atomsM-ok (Sb⁻0-3-1-2)  = Eq.refl
atomsM-ok (Sb0-3-42-1)  = Eq.refl
atomsM-ok (Sb0-4-1-2)   = Eq.refl
atomsM-ok (Sb0-4-2-1)   = Eq.refl
atomsM-ok (Sb0-4-3-1)   = Eq.refl
atomsM-ok (Sb⁻0-4-3-1)  = Eq.refl
atomsM-ok (Sb0-4-21-3)  = Eq.refl
atomsM-ok (Sb⁻0-4-2-1)  = Eq.refl
atomsM-ok (Sb0-4-31-2)  = Eq.refl
atomsM-ok (Sb⁻0-4-1-2)  = Eq.refl
atomsM-ok (Sb0-4-32-1)  = Eq.refl
atomsM-ok (Sb1-0-3-2)   = Eq.refl
atomsM-ok (Sb⁻1-0-3-2)  = Eq.refl
atomsM-ok (Sb1-0-42-3)  = Eq.refl
atomsM-ok (Sb1-2-0-3)   = Eq.refl
atomsM-ok (Sb⁻1-2-0-3)  = Eq.refl
atomsM-ok (Sb1-2-43-0)  = Eq.refl
atomsM-ok (Sb1-4-3-0)   = Eq.refl
atomsM-ok (Sb⁻1-4-3-0)  = Eq.refl
atomsM-ok (Sb1-4-20-3)  = Eq.refl
atomsM-ok (Sb2-0-3-1)   = Eq.refl
atomsM-ok (Sb⁻2-0-3-1)  = Eq.refl
atomsM-ok (Sb2-0-41-3)  = Eq.refl
atomsM-ok (Sb2-1-0-3)   = Eq.refl
atomsM-ok (Sb⁻2-1-0-3)  = Eq.refl
atomsM-ok (Sb2-1-43-0)  = Eq.refl
atomsM-ok (Sb2-4-3-1)   = Eq.refl
atomsM-ok (Sb⁻2-4-3-1)  = Eq.refl
atomsM-ok (Sb2-4-01-3)  = Eq.refl
atomsM-ok (Sb2-4-3-0)   = Eq.refl
atomsM-ok (Sb⁻2-4-3-0)  = Eq.refl
atomsM-ok (Sb2-4-10-3)  = Eq.refl
atomsM-ok (Sb3-0-4-2)   = Eq.refl
atomsM-ok (Sb⁻3-0-4-2)  = Eq.refl
atomsM-ok (Sb3-0-12-4)  = Eq.refl
atomsM-ok (Sb3-0-2-1)   = Eq.refl
atomsM-ok (Sb3-0-4-1)   = Eq.refl
atomsM-ok (Sb⁻3-0-4-1)  = Eq.refl
atomsM-ok (Sb3-0-21-4)  = Eq.refl
atomsM-ok (Sb⁻3-0-2-1)  = Eq.refl
atomsM-ok (Sb3-0-41-2)  = Eq.refl
atomsM-ok (Sb3-1-0-2)   = Eq.refl
atomsM-ok (Sb3-1-4-2)   = Eq.refl
atomsM-ok (Sb⁻3-1-4-2)  = Eq.refl
atomsM-ok (Sb3-1-02-4)  = Eq.refl
atomsM-ok (Sb⁻3-1-0-2)  = Eq.refl
atomsM-ok (Sb3-1-42-0)  = Eq.refl
atomsM-ok (Sb3-4-2-1)   = Eq.refl
atomsM-ok (Sb⁻3-4-2-1)  = Eq.refl
atomsM-ok (Sb3-4-01-2)  = Eq.refl
atomsM-ok (Sb4-0-3-2)   = Eq.refl
atomsM-ok (Sb⁻4-0-3-2)  = Eq.refl
atomsM-ok (Sb4-0-12-3)  = Eq.refl
atomsM-ok (Sb4-0-2-1)   = Eq.refl
atomsM-ok (Sb4-0-3-1)   = Eq.refl
atomsM-ok (Sb⁻4-0-3-1)  = Eq.refl
atomsM-ok (Sb4-0-21-3)  = Eq.refl
atomsM-ok (Sb⁻4-0-2-1)  = Eq.refl
atomsM-ok (Sb4-0-31-2)  = Eq.refl
atomsM-ok (Sb4-1-0-2)   = Eq.refl
atomsM-ok (Sb4-1-0-3)   = Eq.refl
atomsM-ok (Sb4-1-3-2)   = Eq.refl
atomsM-ok (Sb⁻4-1-3-2)  = Eq.refl
atomsM-ok (Sb4-1-02-3)  = Eq.refl
atomsM-ok (Sb⁻4-1-0-3)  = Eq.refl
atomsM-ok (Sb4-1-23-0)  = Eq.refl
atomsM-ok (Sb⁻4-1-0-2)  = Eq.refl
atomsM-ok (Sb4-1-32-0)  = Eq.refl
atomsM-ok (Sb4-2-0-3)   = Eq.refl
atomsM-ok (Sb4-2-1-3)   = Eq.refl
atomsM-ok (Sb⁻4-2-1-3)  = Eq.refl
atomsM-ok (Sb4-2-03-1)  = Eq.refl
atomsM-ok (Sb⁻4-2-0-3)  = Eq.refl
atomsM-ok (Sb4-2-13-0)  = Eq.refl
atomsM-ok (Sb⁻2-0-41-3) = Eq.refl

atomsL : List Mac → List At
atomsL []       = []
atomsL (x ∷ xs) = atomsM x ++ atomsL xs

eqLA : List At → List At → Bool
eqLA []       []       = true
eqLA []       (y ∷ ys) = false
eqLA (x ∷ xs) []       = false
eqLA (x ∷ xs) (y ∷ ys) = (codeA x ≡ᵇ codeA y) ∧ eqLA xs ys

private
  eqLA-sound : (xs ys : List At) → eqLA xs ys ≡ true → xs ≡ ys
  eqLA-sound []       []       h = Eq.refl
  eqLA-sound []       (y ∷ ys) ()
  eqLA-sound (x ∷ xs) []       ()
  eqLA-sound (x ∷ xs) (y ∷ ys) h with codeA x ≡ᵇ codeA y in e
  eqLA-sound (x ∷ xs) (y ∷ ys) h  | true  =
    Eq.cong₂ _∷_
      (Eq.trans (Eq.sym (decode-codeA x))
        (Eq.trans (Eq.cong decodeA (≡ᵇ-sound (codeA x) (codeA y) e)) (decode-codeA y)))
      (eqLA-sound xs ys h)
  eqLA-sound (x ∷ xs) (y ∷ ys) () | false

  ++-[] : (xs : List (Gen 5)) → xs ++ [] ≡ xs
  ++-[] []       = Eq.refl
  ++-[] (x ∷ xs) = Eq.cong (x ∷_) (++-[] xs)

  ++-assoc : (xs ys zs : List (Gen 5)) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
  ++-assoc []       ys zs = Eq.refl
  ++-assoc (x ∷ xs) ys zs = Eq.cong (x ∷_) (++-assoc xs ys zs)

  flat-∷ : (x : Mac) (xs : List Mac) → flat (x ∷ xs) ≡ flat (x ∷ []) ++ flat xs
  flat-∷ x []       = Eq.sym (++-[] (flat (x ∷ [])))
  flat-∷ x (m ∷ ms) = Eq.refl

  flatA-++ : (as bs : List At) → flatA (as ++ bs) ≡ flatA as ++ flatA bs
  flatA-++ []       bs = Eq.refl
  flatA-++ (a ∷ as) bs =
    Eq.trans (Eq.cong (to-list (exA a) ++_) (flatA-++ as bs))
      (Eq.sym (++-assoc (to-list (exA a)) (flatA as) (flatA bs)))

  flat-atoms : (xs : List Mac) → flat xs ≡ flatA (atomsL xs)
  flat-atoms []       = Eq.refl
  flat-atoms (x ∷ xs) =
    Eq.trans (flat-∷ x xs)
      (Eq.trans (Eq.cong₂ _++_ (atomsM-ok x) (flat-atoms xs))
        (Eq.sym (flatA-++ (atomsM x) (atomsL xs))))

------------------------------------------------------------------------
-- Whether two runs of letters spell the same generators

-- The same atoms, or else the same generators.
sameG : List Mac → List Mac → Bool
sameG xs ys = if eqLA (atomsL xs) (atomsL ys) then true else eqLG (flat xs) (flat ys)

sameG-ok : (xs ys : List Mac) → sameG xs ys ≡ true → flat xs ≡ flat ys
sameG-ok xs ys h with eqLA (atomsL xs) (atomsL ys) in e
sameG-ok xs ys h  | true  =
  Eq.trans (flat-atoms xs) (Eq.trans (Eq.cong flatA (eqLA-sound (atomsL xs) (atomsL ys) e)) (Eq.sym (flat-atoms ys)))
sameG-ok xs ys h  | false = eqLG-sound (flat xs) (flat ys) h

------------------------------------------------------------------------
-- The line as a zipper

-- The letters before the focus, last first, and the letters from it on,
-- with the index of the focus.  A step at position k moves the focus
-- there, which costs the distance from the step before: two letters on
-- average in Four/D and Five/D, whose steps are at positions 30 and 47
-- on average, and the line as a list was walked from its start at every
-- step (take, drop and next).  The equation's sides and the parts of
-- the line are handed on as arguments (runZ-rw, runZ-at, runZ-seg), so
-- that Agda's evaluator computes each once.  The engine is that of
-- Qutrit-Clifford.Engine on the ten-completeness branch.
data Zip : Set where
  zp : ℕ → List Mac → List Mac → Zip

revApp : List Mac → List Mac → List Mac
revApp []       ys = ys
revApp (x ∷ xs) ys = revApp xs (x ∷ ys)

plug : Zip → List Mac
plug (zp _ b a) = revApp b a

goL goR : ℕ → Zip → Maybe Zip
goL zero    z                = just z
goL (suc k) (zp c (x ∷ b) a) = goL k (zp (pred c) b (x ∷ a))
goL (suc k) (zp c [] a)      = nothing
goR zero    z                = just z
goR (suc k) (zp c b (x ∷ a)) = goR k (zp (suc c) (x ∷ b) a)
goR (suc k) (zp c b [])      = nothing

seek : ℕ → Zip → Maybe Zip
seek i (zp c b a) = if i <ᵇ c then goL (c ∸ i) (zp c b a) else goR (i ∸ c) (zp c b a)

-- What follows l in a, when l begins a.
strip : List Mac → List Mac → Maybe (List Mac)
strip []      a       = just a
strip (x ∷ l) []      = nothing
strip (x ∷ l) (y ∷ a) = if codeM x ≡ᵇ codeM y then strip l a else nothing

mutual
  runZ : List Step → Zip → Maybe Zip
  runZ []               z = just z
  runZ (rw k e ∷ ss)    z = runZ-rw ss (lhs e) (rhs e) (seek k z)
  runZ (rw⁻ k e ∷ ss)   z = runZ-rw ss (rhs e) (lhs e) (seek k z)
  runZ (re k n ys ∷ ss) z = runZ-re ss n ys (seek k z)

  runZ-rw : List Step → (l r : List Mac) → Maybe Zip → Maybe Zip
  runZ-rw ss l r nothing           = nothing
  runZ-rw ss l r (just (zp c b a)) = runZ-at ss r c b (strip l a)

  runZ-at : List Step → List Mac → ℕ → List Mac → Maybe (List Mac) → Maybe Zip
  runZ-at ss r c b nothing     = nothing
  runZ-at ss r c b (just rest) = runZ ss (zp c b (r ++ rest))

  runZ-re : List Step → ℕ → List Mac → Maybe Zip → Maybe Zip
  runZ-re ss n ys nothing           = nothing
  runZ-re ss n ys (just (zp c b a)) = runZ-seg ss ys c b (take n a) (drop n a)

  runZ-seg : List Step → List Mac → ℕ → (b seg rest : List Mac) → Maybe Zip
  runZ-seg ss ys c b seg rest =
    if sameG seg ys then runZ ss (zp c b (ys ++ rest)) else nothing

okZ : List Mac → Maybe Zip → Bool
okZ r (just z) = eqLM (plug z) r
okZ r nothing  = false

check : List Step → List Mac → List Mac → Bool
check ss l r = okZ r (runZ ss (zp 0 [] l))

private
  ≡⇒≈ : ∀ {xs ys} → xs ≡ ys → ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
  ≡⇒≈ Eq.refl = refl

  code-eq : ∀ x y → (codeM x ≡ᵇ codeM y) ≡ true → x ≡ y
  code-eq x y e =
    Eq.trans (Eq.sym (decode-codeM x))
      (Eq.trans (Eq.cong decodeM (≡ᵇ-sound (codeM x) (codeM y) e)) (decode-codeM y))

  lc-∷ : ∀ ℓ ls → ⟪ ℓ ∷ ls ⟫ʷ ≈ ⟪ ℓ ⟫ • ⟪ ls ⟫ʷ
  lc-∷ ℓ []       = sym right-unit
  lc-∷ ℓ (m ∷ ls) = refl

  lc-++ : ∀ xs ys → ⟪ xs ++ ys ⟫ʷ ≈ ⟪ xs ⟫ʷ • ⟪ ys ⟫ʷ
  lc-++ []       ys = sym left-unit
  lc-++ (x ∷ xs) ys =
    trans (lc-∷ x (xs ++ ys))
    (trans (back ⟪ x ⟫ (lc-++ xs ys))
    (trans (sym assoc) (front ⟪ ys ⟫ʷ (sym (lc-∷ x xs)))))

  ++-congˡ : ∀ {x y} s → ⟪ x ⟫ʷ ≈ ⟪ y ⟫ʷ → ⟪ x ++ s ⟫ʷ ≈ ⟪ y ++ s ⟫ʷ
  ++-congˡ {x} {y} s e = trans (lc-++ x s) (trans (front ⟪ s ⟫ʷ e) (sym (lc-++ y s)))

  revApp-cong : (b : List Mac) {x y : List Mac} → ⟪ x ⟫ʷ ≈ ⟪ y ⟫ʷ → ⟪ revApp b x ⟫ʷ ≈ ⟪ revApp b y ⟫ʷ
  revApp-cong []      e = e
  revApp-cong (g ∷ b) {x} {y} e =
    revApp-cong b (trans (lc-∷ g x) (trans (back ⟪ g ⟫ e) (sym (lc-∷ g y))))

  take++drop : (n : ℕ) (xs : List Mac) → take n xs ++ drop n xs ≡ xs
  take++drop zero    xs       = Eq.refl
  take++drop (suc n) []       = Eq.refl
  take++drop (suc n) (x ∷ xs) = Eq.cong (x ∷_) (take++drop n xs)

  -- Moving the focus keeps the line.
  goL-un : (k : ℕ) (z z′ : Zip) → goL k z ≡ just z′ → plug z′ ≡ plug z
  goL-un zero    z                z′ Eq.refl = Eq.refl
  goL-un (suc k) (zp c (x ∷ b) a) z′ h       = goL-un k (zp (pred c) b (x ∷ a)) z′ h
  goL-un (suc k) (zp c [] a)      z′ ()

  goR-un : (k : ℕ) (z z′ : Zip) → goR k z ≡ just z′ → plug z′ ≡ plug z
  goR-un zero    z                z′ Eq.refl = Eq.refl
  goR-un (suc k) (zp c b (x ∷ a)) z′ h       = goR-un k (zp (suc c) (x ∷ b) a) z′ h
  goR-un (suc k) (zp c b [])      z′ ()

  seek-un : (i : ℕ) (z z′ : Zip) → seek i z ≡ just z′ → plug z′ ≡ plug z
  seek-un i (zp c b a) z′ h with i <ᵇ c
  seek-un i (zp c b a) z′ h | true  = goL-un (c ∸ i) (zp c b a) z′ h
  seek-un i (zp c b a) z′ h | false = goR-un (i ∸ c) (zp c b a) z′ h

  strip-sound : (l a rest : List Mac) → strip l a ≡ just rest → a ≡ l ++ rest
  strip-sound []      a       rest Eq.refl = Eq.refl
  strip-sound (x ∷ l) []      rest ()
  strip-sound (x ∷ l) (y ∷ a) rest h with codeM x ≡ᵇ codeM y in e
  strip-sound (x ∷ l) (y ∷ a) rest h  | true  =
    Eq.cong₂ _∷_ (Eq.sym (code-eq x y e)) (strip-sound l a rest h)
  strip-sound (x ∷ l) (y ∷ a) rest () | false

  mutual
    runZ-sound : (ss : List Step) (z z′ : Zip) → runZ ss z ≡ just z′ → ⟪ plug z ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-sound []               z z′ Eq.refl = refl
    runZ-sound (rw k e ∷ ss)    z z′ h =
      runZ-rw-sound ss (lhs e) (rhs e) (prf e) z (seek k z) (seek-un k z) z′ h
    runZ-sound (rw⁻ k e ∷ ss)   z z′ h =
      runZ-rw-sound ss (rhs e) (lhs e) (sym (prf e)) z (seek k z) (seek-un k z) z′ h
    runZ-sound (re k n ys ∷ ss) z z′ h =
      runZ-re-sound ss n ys z (seek k z) (seek-un k z) z′ h

    runZ-rw-sound : (ss : List Step) (l r : List Mac) → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ → (z : Zip) (m : Maybe Zip) →
                    (∀ z₁ → m ≡ just z₁ → plug z₁ ≡ plug z) → (z′ : Zip) →
                    runZ-rw ss l r m ≡ just z′ → ⟪ plug z ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-rw-sound ss l r p z nothing           u z′ ()
    runZ-rw-sound ss l r p z (just (zp c b a)) u z′ h =
      trans (≡⇒≈ (Eq.sym (u (zp c b a) Eq.refl)))
            (runZ-at-sound ss l r p c b a (strip l a) Eq.refl z′ h)

    runZ-at-sound : (ss : List Step) (l r : List Mac) → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ → (c : ℕ) (b a : List Mac) →
                    (m : Maybe (List Mac)) → strip l a ≡ m → (z′ : Zip) →
                    runZ-at ss r c b m ≡ just z′ → ⟪ revApp b a ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-at-sound ss l r p c b a nothing     s z′ ()
    runZ-at-sound ss l r p c b a (just rest) s z′ h =
      trans (revApp-cong b (trans (≡⇒≈ (strip-sound l a rest s)) (++-congˡ {l} {r} rest p)))
            (runZ-sound ss (zp c b (r ++ rest)) z′ h)

    runZ-re-sound : (ss : List Step) (n : ℕ) (ys : List Mac) (z : Zip) (m : Maybe Zip) →
                    (∀ z₁ → m ≡ just z₁ → plug z₁ ≡ plug z) → (z′ : Zip) →
                    runZ-re ss n ys m ≡ just z′ → ⟪ plug z ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-re-sound ss n ys z nothing           u z′ ()
    runZ-re-sound ss n ys z (just (zp c b a)) u z′ h =
      trans (≡⇒≈ (Eq.sym (u (zp c b a) Eq.refl)))
      (trans (≡⇒≈ (Eq.cong (revApp b) (Eq.sym (take++drop n a))))
             (runZ-seg-sound ss ys c b (take n a) (drop n a) z′ h))

    runZ-seg-sound : (ss : List Step) (ys : List Mac) (c : ℕ) (b seg rest : List Mac) (z′ : Zip) →
                     runZ-seg ss ys c b seg rest ≡ just z′ → ⟪ revApp b (seg ++ rest) ⟫ʷ ≈ ⟪ plug z′ ⟫ʷ
    runZ-seg-sound ss ys c b seg rest z′ h with sameG seg ys in g
    runZ-seg-sound ss ys c b seg rest z′ h  | true  =
      trans (revApp-cong b (++-congˡ {seg} {ys} rest (by-assoc {⟪ seg ⟫ʷ} {⟪ ys ⟫ʷ} (sameG-ok seg ys g))))
            (runZ-sound ss (zp c b (ys ++ rest)) z′ h)
    runZ-seg-sound ss ys c b seg rest z′ () | false

check-sound : (ss : List Step) (l r : List Mac) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
check-sound ss l r h with runZ ss (zp 0 [] l) in e
check-sound ss l r h  | just z  = trans (runZ-sound ss (zp 0 [] l) z e) (≡⇒≈ (eqLM-sound (plug z) r h))
check-sound ss l r () | nothing

-- The equation of a derivation, checked by running it.
derive : (l r : List Mac) (ss : List Step) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
derive l r ss h = check-sound ss l r h
