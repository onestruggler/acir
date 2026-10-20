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
-- only a re-bracketing compares generators.  `derive l r ss Eq.refl`
-- checks the whole run in one evaluation, its result compared with r
-- inside it, and gives ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ.  Written by
-- `scratchpad/five/reflect5.py`.
------------------------------------------------------------------------

{-# OPTIONS --without-K --safe #-}

module Examples.Groups.Clifford+CS.Five.Reflect where

open import Data.Bool.Base using (Bool ; true ; false ; if_then_else_ ; _∧_ ; T)
open import Data.List.Base using (List ; [] ; _∷_ ; _++_ ; length ; take ; drop)
open import Data.Maybe.Base using (Maybe ; just ; nothing)
open import Data.Nat.Base using (ℕ ; zero ; suc ; _≡ᵇ_)
open import Data.Nat.Properties using (≡ᵇ⇒≡)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)

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
codeM (Bx1-04)      = 186
codeM (Bx0-124)     = 187
codeM (Bx0-13)      = 188
codeM (Bx1-043)     = 189
codeM (Bx0-1243)    = 190
codeM (Bx1-02)      = 191
codeM (Bx0-132)     = 192
codeM (Bx1-024)     = 193
codeM (Bx0-1324)    = 194
codeM (Bx0-134)     = 195
codeM (Bx1-042)     = 196
codeM (Bx0-1342)    = 197
codeM (Bx0-142)     = 198
codeM (Bx1-023)     = 199
codeM (Bx0-1423)    = 200
codeM (Bx0-143)     = 201
codeM (Bx1-032)     = 202
codeM (Bx0-1432)    = 203
codeM (Bx0-21)      = 204
codeM (Bx2-03)      = 205
codeM (Bx0-213)     = 206
codeM (Bx0-24)      = 207
codeM (Bx2-034)     = 208
codeM (Bx0-2134)    = 209
codeM (Bx2-04)      = 210
codeM (Bx0-214)     = 211
codeM (Bx0-23)      = 212
codeM (Bx2-043)     = 213
codeM (Bx0-2143)    = 214
codeM (Bx2-01)      = 215
codeM (Bx0-231)     = 216
codeM (Bx2-014)     = 217
codeM (Bx0-2314)    = 218
codeM (Bx0-234)     = 219
codeM (Bx2-041)     = 220
codeM (Bx0-2341)    = 221
codeM (Bx0-241)     = 222
codeM (Bx2-013)     = 223
codeM (Bx0-2413)    = 224
codeM (Bx0-243)     = 225
codeM (Bx2-031)     = 226
codeM (Bx0-2431)    = 227
codeM (Bx0-31)      = 228
codeM (Bx3-02)      = 229
codeM (Bx0-312)     = 230
codeM (Bx0-34)      = 231
codeM (Bx3-024)     = 232
codeM (Bx0-3124)    = 233
codeM (Bx3-04)      = 234
codeM (Bx0-314)     = 235
codeM (Bx0-32)      = 236
codeM (Bx3-042)     = 237
codeM (Bx0-3142)    = 238
codeM (Bx3-01)      = 239
codeM (Bx0-321)     = 240
codeM (Bx3-014)     = 241
codeM (Bx0-3214)    = 242
codeM (Bx0-324)     = 243
codeM (Bx3-041)     = 244
codeM (Bx0-3241)    = 245
codeM (Bx0-341)     = 246
codeM (Bx3-012)     = 247
codeM (Bx0-3412)    = 248
codeM (Bx0-342)     = 249
codeM (Bx3-021)     = 250
codeM (Bx0-3421)    = 251
codeM (Bx0-41)      = 252
codeM (Bx4-02)      = 253
codeM (Bx0-412)     = 254
codeM (Bx0-43)      = 255
codeM (Bx4-023)     = 256
codeM (Bx0-4123)    = 257
codeM (Bx4-03)      = 258
codeM (Bx0-413)     = 259
codeM (Bx0-42)      = 260
codeM (Bx4-032)     = 261
codeM (Bx0-4132)    = 262
codeM (Bx4-01)      = 263
codeM (Bx0-421)     = 264
codeM (Bx4-013)     = 265
codeM (Bx0-4213)    = 266
codeM (Bx0-423)     = 267
codeM (Bx4-031)     = 268
codeM (Bx0-4231)    = 269
codeM (Bx0-431)     = 270
codeM (Bx4-012)     = 271
codeM (Bx0-4312)    = 272
codeM (Bx0-432)     = 273
codeM (Bx4-021)     = 274
codeM (Bx0-4321)    = 275
codeM (Bx1-0234)    = 276
codeM (Bx1-0243)    = 277
codeM (Bx1-0324)    = 278
codeM (Bx1-0342)    = 279
codeM (Bx1-0423)    = 280
codeM (Bx1-0432)    = 281
codeM (Bx1-20)      = 282
codeM (Bx2-13)      = 283
codeM (Bx1-203)     = 284
codeM (Bx1-24)      = 285
codeM (Bx2-134)     = 286
codeM (Bx1-2034)    = 287
codeM (Bx2-14)      = 288
codeM (Bx1-204)     = 289
codeM (Bx1-23)      = 290
codeM (Bx2-143)     = 291
codeM (Bx1-2043)    = 292
codeM (Bx2-10)      = 293
codeM (Bx1-230)     = 294
codeM (Bx2-104)     = 295
codeM (Bx1-2304)    = 296
codeM (Bx1-234)     = 297
codeM (Bx2-140)     = 298
codeM (Bx1-2340)    = 299
codeM (Bx1-240)     = 300
codeM (Bx2-103)     = 301
codeM (Bx1-2403)    = 302
codeM (Bx1-243)     = 303
codeM (Bx2-130)     = 304
codeM (Bx1-2430)    = 305
codeM (Bx1-30)      = 306
codeM (Bx3-12)      = 307
codeM (Bx1-302)     = 308
codeM (Bx1-34)      = 309
codeM (Bx3-124)     = 310
codeM (Bx1-3024)    = 311
codeM (Bx3-14)      = 312
codeM (Bx1-304)     = 313
codeM (Bx1-32)      = 314
codeM (Bx3-142)     = 315
codeM (Bx1-3042)    = 316
codeM (Bx3-10)      = 317
codeM (Bx1-320)     = 318
codeM (Bx3-104)     = 319
codeM (Bx1-3204)    = 320
codeM (Bx1-324)     = 321
codeM (Bx3-140)     = 322
codeM (Bx1-3240)    = 323
codeM (Bx1-340)     = 324
codeM (Bx3-102)     = 325
codeM (Bx1-3402)    = 326
codeM (Bx1-342)     = 327
codeM (Bx3-120)     = 328
codeM (Bx1-3420)    = 329
codeM (Bx1-40)      = 330
codeM (Bx4-12)      = 331
codeM (Bx1-402)     = 332
codeM (Bx1-43)      = 333
codeM (Bx4-123)     = 334
codeM (Bx1-4023)    = 335
codeM (Bx4-13)      = 336
codeM (Bx1-403)     = 337
codeM (Bx1-42)      = 338
codeM (Bx4-132)     = 339
codeM (Bx1-4032)    = 340
codeM (Bx4-10)      = 341
codeM (Bx1-420)     = 342
codeM (Bx4-103)     = 343
codeM (Bx1-4203)    = 344
codeM (Bx1-423)     = 345
codeM (Bx4-130)     = 346
codeM (Bx1-4230)    = 347
codeM (Bx1-430)     = 348
codeM (Bx4-102)     = 349
codeM (Bx1-4302)    = 350
codeM (Bx1-432)     = 351
codeM (Bx4-120)     = 352
codeM (Bx1-4320)    = 353
codeM (Bx2-0134)    = 354
codeM (Bx2-0143)    = 355
codeM (Bx2-0314)    = 356
codeM (Bx2-0341)    = 357
codeM (Bx2-0413)    = 358
codeM (Bx2-0431)    = 359
codeM (Bx2-1034)    = 360
codeM (Bx2-1043)    = 361
codeM (Bx2-1304)    = 362
codeM (Bx2-1340)    = 363
codeM (Bx2-1403)    = 364
codeM (Bx2-1430)    = 365
codeM (Bx2-30)      = 366
codeM (Bx3-21)      = 367
codeM (Bx2-301)     = 368
codeM (Bx2-34)      = 369
codeM (Bx3-214)     = 370
codeM (Bx2-3014)    = 371
codeM (Bx3-24)      = 372
codeM (Bx2-304)     = 373
codeM (Bx2-31)      = 374
codeM (Bx3-241)     = 375
codeM (Bx2-3041)    = 376
codeM (Bx3-20)      = 377
codeM (Bx2-310)     = 378
codeM (Bx3-204)     = 379
codeM (Bx2-3104)    = 380
codeM (Bx2-314)     = 381
codeM (Bx3-240)     = 382
codeM (Bx2-3140)    = 383
codeM (Bx2-340)     = 384
codeM (Bx3-201)     = 385
codeM (Bx2-3401)    = 386
codeM (Bx2-341)     = 387
codeM (Bx3-210)     = 388
codeM (Bx2-3410)    = 389
codeM (Bx2-40)      = 390
codeM (Bx4-21)      = 391
codeM (Bx2-401)     = 392
codeM (Bx2-43)      = 393
codeM (Bx4-213)     = 394
codeM (Bx2-4013)    = 395
codeM (Bx4-23)      = 396
codeM (Bx2-403)     = 397
codeM (Bx2-41)      = 398
codeM (Bx4-231)     = 399
codeM (Bx2-4031)    = 400
codeM (Bx4-20)      = 401
codeM (Bx2-410)     = 402
codeM (Bx4-203)     = 403
codeM (Bx2-4103)    = 404
codeM (Bx2-413)     = 405
codeM (Bx4-230)     = 406
codeM (Bx2-4130)    = 407
codeM (Bx2-430)     = 408
codeM (Bx4-201)     = 409
codeM (Bx2-4301)    = 410
codeM (Bx2-431)     = 411
codeM (Bx4-210)     = 412
codeM (Bx2-4310)    = 413
codeM (Bx3-0124)    = 414
codeM (Bx3-0142)    = 415
codeM (Bx3-0214)    = 416
codeM (Bx3-0241)    = 417
codeM (Bx3-0412)    = 418
codeM (Bx3-0421)    = 419
codeM (Bx3-1024)    = 420
codeM (Bx3-1042)    = 421
codeM (Bx3-1204)    = 422
codeM (Bx3-1240)    = 423
codeM (Bx3-1402)    = 424
codeM (Bx3-1420)    = 425
codeM (Bx3-2014)    = 426
codeM (Bx3-2041)    = 427
codeM (Bx3-2104)    = 428
codeM (Bx3-2140)    = 429
codeM (Bx3-2401)    = 430
codeM (Bx3-2410)    = 431
codeM (Bx3-40)      = 432
codeM (Bx3-42)      = 433
codeM (Bx4-312)     = 434
codeM (Bx3-4012)    = 435
codeM (Bx4-32)      = 436
codeM (Bx3-402)     = 437
codeM (Bx3-41)      = 438
codeM (Bx4-321)     = 439
codeM (Bx3-4021)    = 440
codeM (Bx4-302)     = 441
codeM (Bx3-4102)    = 442
codeM (Bx3-412)     = 443
codeM (Bx4-320)     = 444
codeM (Bx3-4120)    = 445
codeM (Bx4-30)      = 446
codeM (Bx3-420)     = 447
codeM (Bx4-301)     = 448
codeM (Bx3-4201)    = 449
codeM (Bx4-31)      = 450
codeM (Bx3-421)     = 451
codeM (Bx4-310)     = 452
codeM (Bx3-4210)    = 453
codeM (Bx4-0123)    = 454
codeM (Bx4-0132)    = 455
codeM (Bx4-0213)    = 456
codeM (Bx4-0231)    = 457
codeM (Bx4-0312)    = 458
codeM (Bx4-0321)    = 459
codeM (Bx4-1023)    = 460
codeM (Bx4-1032)    = 461
codeM (Bx4-1203)    = 462
codeM (Bx4-1230)    = 463
codeM (Bx4-1302)    = 464
codeM (Bx4-1320)    = 465
codeM (Bx4-2013)    = 466
codeM (Bx4-2031)    = 467
codeM (Bx4-2103)    = 468
codeM (Bx4-2130)    = 469
codeM (Bx4-2301)    = 470
codeM (Bx4-2310)    = 471
codeM (Bx4-3012)    = 472
codeM (Bx4-3021)    = 473
codeM (Bx4-3102)    = 474
codeM (Bx4-3120)    = 475
codeM (Bx⁻0-12)     = 476
codeM (Bx⁻1-03)     = 477
codeM (Bx⁻0-123)    = 478
codeM (Bx⁻0-14)     = 479
codeM (Bx⁻1-034)    = 480
codeM (Bx⁻0-1234)   = 481
codeM (Bx⁻1-04)     = 482
codeM (Bx⁻0-124)    = 483
codeM (Bx⁻0-13)     = 484
codeM (Bx⁻1-043)    = 485
codeM (Bx⁻0-1243)   = 486
codeM (Bx⁻1-02)     = 487
codeM (Bx⁻0-132)    = 488
codeM (Bx⁻1-024)    = 489
codeM (Bx⁻0-1324)   = 490
codeM (Bx⁻0-134)    = 491
codeM (Bx⁻1-042)    = 492
codeM (Bx⁻0-1342)   = 493
codeM (Bx⁻0-142)    = 494
codeM (Bx⁻1-023)    = 495
codeM (Bx⁻0-1423)   = 496
codeM (Bx⁻0-143)    = 497
codeM (Bx⁻1-032)    = 498
codeM (Bx⁻0-1432)   = 499
codeM (Bx⁻0-21)     = 500
codeM (Bx⁻2-03)     = 501
codeM (Bx⁻0-213)    = 502
codeM (Bx⁻0-24)     = 503
codeM (Bx⁻2-034)    = 504
codeM (Bx⁻0-2134)   = 505
codeM (Bx⁻2-04)     = 506
codeM (Bx⁻0-214)    = 507
codeM (Bx⁻2-01)     = 508
codeM (Bx⁻0-231)    = 509
codeM (Bx⁻0-234)    = 510
codeM (Bx⁻2-041)    = 511
codeM (Bx⁻0-2341)   = 512
codeM (Bx⁻0-241)    = 513
codeM (Bx⁻0-243)    = 514
codeM (Bx⁻2-031)    = 515
codeM (Bx⁻0-2431)   = 516
codeM (Bx⁻3-02)     = 517
codeM (Bx⁻0-312)    = 518
codeM (Bx⁻0-34)     = 519
codeM (Bx⁻3-024)    = 520
codeM (Bx⁻0-3124)   = 521
codeM (Bx⁻3-01)     = 522
codeM (Bx⁻0-321)    = 523
codeM (Bx⁻3-04)     = 524
codeM (Bx⁻0-324)    = 525
codeM (Bx⁻4-02)     = 526
codeM (Bx⁻0-412)    = 527
codeM (Bx⁻0-43)     = 528
codeM (Bx⁻4-023)    = 529
codeM (Bx⁻0-4123)   = 530
codeM (Bx⁻4-03)     = 531
codeM (Bx⁻0-413)    = 532
codeM (Bx⁻4-01)     = 533
codeM (Bx⁻0-421)    = 534
codeM (Bx⁻0-423)    = 535
codeM (Bx⁻0-431)    = 536
codeM (Bx⁻0-432)    = 537
codeM (Bx⁻1-0234)   = 538
codeM (Bx⁻1-0243)   = 539
codeM (Bx⁻1-0324)   = 540
codeM (Bx⁻1-0342)   = 541
codeM (Bx⁻1-0423)   = 542
codeM (Bx⁻1-0432)   = 543
codeM (Bx⁻1-20)     = 544
codeM (Bx⁻2-13)     = 545
codeM (Bx⁻1-203)    = 546
codeM (Bx⁻1-24)     = 547
codeM (Bx⁻2-134)    = 548
codeM (Bx⁻1-2034)   = 549
codeM (Bx⁻1-23)     = 550
codeM (Bx⁻2-140)    = 551
codeM (Bx⁻1-2340)   = 552
codeM (Bx⁻2-10)     = 553
codeM (Bx⁻1-240)    = 554
codeM (Bx⁻2-103)    = 555
codeM (Bx⁻1-2403)   = 556
codeM (Bx⁻1-34)     = 557
codeM (Bx⁻3-124)    = 558
codeM (Bx⁻1-3024)   = 559
codeM (Bx⁻1-32)     = 560
codeM (Bx⁻3-102)    = 561
codeM (Bx⁻1-3402)   = 562
codeM (Bx⁻1-43)     = 563
codeM (Bx⁻4-123)    = 564
codeM (Bx⁻1-4023)   = 565
codeM (Bx⁻1-42)     = 566
codeM (Bx⁻4-10)     = 567
codeM (Bx⁻1-420)    = 568
codeM (Bx⁻4-103)    = 569
codeM (Bx⁻1-4203)   = 570
codeM (Bx⁻1-430)    = 571
codeM (Bx⁻4-102)    = 572
codeM (Bx⁻1-4302)   = 573
codeM (Bx⁻2-0134)   = 574
codeM (Bx⁻2-0143)   = 575
codeM (Bx⁻2-0314)   = 576
codeM (Bx⁻2-0341)   = 577
codeM (Bx⁻2-0413)   = 578
codeM (Bx⁻2-0431)   = 579
codeM (Bx⁻2-1340)   = 580
codeM (Bx⁻2-1403)   = 581
codeM (Bx⁻2-34)     = 582
codeM (Bx⁻3-214)    = 583
codeM (Bx⁻2-3014)   = 584
codeM (Bx⁻2-43)     = 585
codeM (Bx⁻4-213)    = 586
codeM (Bx⁻2-4013)   = 587
codeM (Bx⁻4-203)    = 588
codeM (Bx⁻2-4103)   = 589
codeM (Bx⁻3-0124)   = 590
codeM (Bx⁻3-0412)   = 591
codeM (Bx⁻3-0421)   = 592
codeM (Bx⁻4-0123)   = 593
codeM (Bx⁻4-0132)   = 594
codeM (Bx⁻4-0213)   = 595
codeM (Bx⁻4-0231)   = 596
codeM (Bx⁻4-0312)   = 597
codeM (Bx⁻4-0321)   = 598
codeM (Bx⁻4-1230)   = 599
codeM (Bx⁻4-1320)   = 600
codeM (Sb0-1-2-3)   = 601
codeM (Sb0-1-2-4)   = 602
codeM (Sb0-1-4-3)   = 603
codeM (Sb⁻0-1-4-3)  = 604
codeM (Sb0-1-23-4)  = 605
codeM (Sb0-1-3-2)   = 606
codeM (Sb0-1-3-4)   = 607
codeM (Sb0-1-4-2)   = 608
codeM (Sb⁻0-1-4-2)  = 609
codeM (Sb0-1-32-4)  = 610
codeM (Sb⁻0-1-2-4)  = 611
codeM (Sb0-1-34-2)  = 612
codeM (Sb⁻0-1-3-2)  = 613
codeM (Sb0-1-42-3)  = 614
codeM (Sb⁻0-1-2-3)  = 615
codeM (Sb0-1-43-2)  = 616
codeM (Sb0-2-1-3)   = 617
codeM (Sb0-2-1-4)   = 618
codeM (Sb0-2-4-3)   = 619
codeM (Sb⁻0-2-4-3)  = 620
codeM (Sb0-2-13-4)  = 621
codeM (Sb0-2-3-1)   = 622
codeM (Sb0-2-4-1)   = 623
codeM (Sb⁻0-2-4-1)  = 624
codeM (Sb0-2-31-4)  = 625
codeM (Sb⁻0-2-1-4)  = 626
codeM (Sb0-2-34-1)  = 627
codeM (Sb⁻0-2-3-1)  = 628
codeM (Sb0-2-41-3)  = 629
codeM (Sb⁻0-2-1-3)  = 630
codeM (Sb0-2-43-1)  = 631
codeM (Sb0-3-1-2)   = 632
codeM (Sb0-3-1-4)   = 633
codeM (Sb0-3-4-2)   = 634
codeM (Sb⁻0-3-4-2)  = 635
codeM (Sb0-3-12-4)  = 636
codeM (Sb0-3-2-4)   = 637
codeM (Sb⁻0-3-2-4)  = 638
codeM (Sb0-3-14-2)  = 639
codeM (Sb0-3-2-1)   = 640
codeM (Sb0-3-4-1)   = 641
codeM (Sb⁻0-3-4-1)  = 642
codeM (Sb0-3-21-4)  = 643
codeM (Sb⁻0-3-1-4)  = 644
codeM (Sb0-3-24-1)  = 645
codeM (Sb0-4-1-2)   = 646
codeM (Sb0-4-1-3)   = 647
codeM (Sb0-4-3-2)   = 648
codeM (Sb⁻0-4-3-2)  = 649
codeM (Sb0-4-12-3)  = 650
codeM (Sb0-4-2-1)   = 651
codeM (Sb0-4-3-1)   = 652
codeM (Sb⁻0-4-3-1)  = 653
codeM (Sb0-4-21-3)  = 654
codeM (Sb1-0-2-3)   = 655
codeM (Sb1-0-2-4)   = 656
codeM (Sb1-0-4-3)   = 657
codeM (Sb⁻1-0-4-3)  = 658
codeM (Sb1-0-23-4)  = 659
codeM (Sb1-0-3-4)   = 660
codeM (Sb⁻1-0-3-4)  = 661
codeM (Sb1-0-24-3)  = 662
codeM (Sb1-0-3-2)   = 663
codeM (Sb1-0-4-2)   = 664
codeM (Sb⁻1-0-4-2)  = 665
codeM (Sb1-0-32-4)  = 666
codeM (Sb⁻1-0-2-4)  = 667
codeM (Sb1-0-34-2)  = 668
codeM (Sb⁻1-0-3-2)  = 669
codeM (Sb1-0-42-3)  = 670
codeM (Sb⁻1-0-2-3)  = 671
codeM (Sb1-0-43-2)  = 672
codeM (Sb1-2-0-3)   = 673
codeM (Sb1-2-0-4)   = 674
codeM (Sb1-2-4-3)   = 675
codeM (Sb⁻1-2-4-3)  = 676
codeM (Sb1-2-03-4)  = 677
codeM (Sb1-2-3-4)   = 678
codeM (Sb⁻1-2-3-4)  = 679
codeM (Sb1-2-04-3)  = 680
codeM (Sb1-2-3-0)   = 681
codeM (Sb⁻1-2-0-4)  = 682
codeM (Sb1-2-34-0)  = 683
codeM (Sb1-2-4-0)   = 684
codeM (Sb⁻1-2-3-0)  = 685
codeM (Sb1-2-40-3)  = 686
codeM (Sb⁻1-2-0-3)  = 687
codeM (Sb1-2-43-0)  = 688
codeM (Sb1-3-0-4)   = 689
codeM (Sb1-3-2-4)   = 690
codeM (Sb⁻1-3-2-4)  = 691
codeM (Sb1-3-04-2)  = 692
codeM (Sb1-3-2-0)   = 693
codeM (Sb⁻1-3-0-4)  = 694
codeM (Sb1-3-24-0)  = 695
codeM (Sb1-3-4-0)   = 696
codeM (Sb⁻1-3-2-0)  = 697
codeM (Sb1-3-40-2)  = 698
codeM (Sb1-4-2-0)   = 699
codeM (Sb1-4-3-0)   = 700
codeM (Sb⁻1-4-3-0)  = 701
codeM (Sb1-4-20-3)  = 702
codeM (Sb⁻1-4-2-0)  = 703
codeM (Sb1-4-30-2)  = 704
codeM (Sb2-0-1-3)   = 705
codeM (Sb2-0-1-4)   = 706
codeM (Sb2-0-4-3)   = 707
codeM (Sb⁻2-0-4-3)  = 708
codeM (Sb2-0-13-4)  = 709
codeM (Sb2-0-3-4)   = 710
codeM (Sb⁻2-0-3-4)  = 711
codeM (Sb2-0-14-3)  = 712
codeM (Sb2-0-3-1)   = 713
codeM (Sb2-0-4-1)   = 714
codeM (Sb⁻2-0-4-1)  = 715
codeM (Sb2-0-31-4)  = 716
codeM (Sb⁻2-0-1-4)  = 717
codeM (Sb2-0-34-1)  = 718
codeM (Sb⁻2-0-3-1)  = 719
codeM (Sb2-0-41-3)  = 720
codeM (Sb⁻2-0-1-3)  = 721
codeM (Sb2-0-43-1)  = 722
codeM (Sb2-1-0-3)   = 723
codeM (Sb2-1-0-4)   = 724
codeM (Sb2-1-3-0)   = 725
codeM (Sb⁻2-1-0-4)  = 726
codeM (Sb2-1-34-0)  = 727
codeM (Sb2-1-4-0)   = 728
codeM (Sb⁻2-1-3-0)  = 729
codeM (Sb2-1-40-3)  = 730
codeM (Sb⁻2-1-0-3)  = 731
codeM (Sb2-1-43-0)  = 732
codeM (Sb2-3-0-1)   = 733
codeM (Sb2-3-0-4)   = 734
codeM (Sb2-3-1-4)   = 735
codeM (Sb⁻2-3-1-4)  = 736
codeM (Sb2-3-04-1)  = 737
codeM (Sb2-3-1-0)   = 738
codeM (Sb⁻2-3-0-4)  = 739
codeM (Sb2-3-14-0)  = 740
codeM (Sb⁻2-3-1-0)  = 741
codeM (Sb2-3-40-1)  = 742
codeM (Sb⁻2-3-0-1)  = 743
codeM (Sb2-3-41-0)  = 744
codeM (Sb2-4-0-1)   = 745
codeM (Sb2-4-3-1)   = 746
codeM (Sb⁻2-4-3-1)  = 747
codeM (Sb2-4-01-3)  = 748
codeM (Sb2-4-1-0)   = 749
codeM (Sb2-4-3-0)   = 750
codeM (Sb⁻2-4-3-0)  = 751
codeM (Sb2-4-10-3)  = 752
codeM (Sb⁻2-4-1-0)  = 753
codeM (Sb2-4-30-1)  = 754
codeM (Sb⁻2-4-0-1)  = 755
codeM (Sb2-4-31-0)  = 756
codeM (Sb3-0-1-2)   = 757
codeM (Sb3-0-1-4)   = 758
codeM (Sb3-0-2-4)   = 759
codeM (Sb⁻3-0-2-4)  = 760
codeM (Sb3-0-14-2)  = 761
codeM (Sb3-0-2-1)   = 762
codeM (Sb3-0-4-1)   = 763
codeM (Sb⁻3-0-4-1)  = 764
codeM (Sb3-0-21-4)  = 765
codeM (Sb⁻3-0-1-4)  = 766
codeM (Sb3-0-24-1)  = 767
codeM (Sb⁻3-0-2-1)  = 768
codeM (Sb3-0-41-2)  = 769
codeM (Sb⁻3-0-1-2)  = 770
codeM (Sb3-0-42-1)  = 771
codeM (Sb3-1-0-2)   = 772
codeM (Sb3-1-0-4)   = 773
codeM (Sb3-1-2-0)   = 774
codeM (Sb3-1-4-0)   = 775
codeM (Sb⁻3-1-2-0)  = 776
codeM (Sb3-1-40-2)  = 777
codeM (Sb⁻3-1-0-2)  = 778
codeM (Sb3-1-42-0)  = 779
codeM (Sb3-2-0-1)   = 780
codeM (Sb3-2-1-0)   = 781
codeM (Sb⁻3-2-1-0)  = 782
codeM (Sb3-2-40-1)  = 783
codeM (Sb⁻3-2-0-1)  = 784
codeM (Sb3-2-41-0)  = 785
codeM (Sb3-4-0-1)   = 786
codeM (Sb3-4-0-2)   = 787
codeM (Sb3-4-2-1)   = 788
codeM (Sb⁻3-4-2-1)  = 789
codeM (Sb3-4-01-2)  = 790
codeM (Sb3-4-1-0)   = 791
codeM (Sb3-4-2-0)   = 792
codeM (Sb⁻3-4-2-0)  = 793
codeM (Sb3-4-10-2)  = 794
codeM (Sb⁻3-4-0-2)  = 795
codeM (Sb3-4-12-0)  = 796
codeM (Sb⁻3-4-1-0)  = 797
codeM (Sb3-4-20-1)  = 798
codeM (Sb⁻3-4-0-1)  = 799
codeM (Sb3-4-21-0)  = 800
codeM (Sb4-0-1-2)   = 801
codeM (Sb4-0-1-3)   = 802
codeM (Sb4-0-3-2)   = 803
codeM (Sb⁻4-0-3-2)  = 804
codeM (Sb4-0-12-3)  = 805
codeM (Sb4-0-2-3)   = 806
codeM (Sb⁻4-0-2-3)  = 807
codeM (Sb4-0-13-2)  = 808
codeM (Sb4-0-2-1)   = 809
codeM (Sb4-0-3-1)   = 810
codeM (Sb⁻4-0-3-1)  = 811
codeM (Sb4-0-21-3)  = 812
codeM (Sb⁻4-0-1-3)  = 813
codeM (Sb4-0-23-1)  = 814
codeM (Sb⁻4-0-2-1)  = 815
codeM (Sb4-0-31-2)  = 816
codeM (Sb⁻4-0-1-2)  = 817
codeM (Sb4-0-32-1)  = 818
codeM (Sb4-1-0-2)   = 819
codeM (Sb4-1-0-3)   = 820
codeM (Sb4-1-3-2)   = 821
codeM (Sb⁻4-1-3-2)  = 822
codeM (Sb4-1-02-3)  = 823
codeM (Sb4-1-2-3)   = 824
codeM (Sb⁻4-1-2-3)  = 825
codeM (Sb4-1-03-2)  = 826
codeM (Sb4-1-2-0)   = 827
codeM (Sb⁻4-1-0-3)  = 828
codeM (Sb4-1-23-0)  = 829
codeM (Sb4-1-3-0)   = 830
codeM (Sb⁻4-1-0-2)  = 831
codeM (Sb4-1-32-0)  = 832
codeM (Sb4-2-0-3)   = 833
codeM (Sb4-2-1-3)   = 834
codeM (Sb⁻4-2-1-3)  = 835
codeM (Sb4-2-03-1)  = 836
codeM (Sb⁻4-2-0-3)  = 837
codeM (Sb4-2-13-0)  = 838
codeM (Sb4-2-3-0)   = 839
codeM (Sb4-3-1-0)   = 840
codeM (Sb4-3-2-0)   = 841
codeM (Sb⁻0-1-23-4) = 842
codeM (Sb⁻0-1-3-4)  = 843
codeM (Sb⁻0-1-32-4) = 844
codeM (Sb⁻0-1-34-2) = 845
codeM (Sb⁻0-1-42-3) = 846
codeM (Sb⁻0-1-43-2) = 847
codeM (Sb⁻0-2-34-1) = 848
codeM (Sb⁻0-2-43-1) = 849
codeM (Sb⁻0-3-1-2)  = 850
codeM (Sb⁻0-3-2-1)  = 851
codeM (Sb⁻0-4-1-2)  = 852
codeM (Sb⁻0-4-1-3)  = 853
codeM (Sb⁻0-4-2-1)  = 854
codeM (Sb⁻1-0-23-4) = 855
codeM (Sb⁻1-0-24-3) = 856
codeM (Sb⁻1-0-32-4) = 857
codeM (Sb⁻1-0-34-2) = 858
codeM (Sb⁻1-0-42-3) = 859
codeM (Sb⁻1-0-43-2) = 860
codeM (Sb⁻1-2-34-0) = 861
codeM (Sb⁻1-2-4-0)  = 862
codeM (Sb⁻1-2-40-3) = 863
codeM (Sb⁻1-3-4-0)  = 864
codeM (Sb⁻1-3-4-2)  = 865
codeM (Sb⁻1-3-40-2) = 866
codeM (Sb⁻1-4-20-3) = 867
codeM (Sb⁻1-4-30-2) = 868
codeM (Sb⁻2-0-13-4) = 869
codeM (Sb⁻2-0-14-3) = 870
codeM (Sb⁻2-0-31-4) = 871
codeM (Sb⁻2-0-34-1) = 872
codeM (Sb⁻2-0-41-3) = 873
codeM (Sb⁻2-0-43-1) = 874
codeM (Sb⁻2-1-34-0) = 875
codeM (Sb⁻2-1-4-0)  = 876
codeM (Sb⁻2-1-40-3) = 877
codeM (Sb⁻2-3-4-0)  = 878
codeM (Sb⁻2-3-4-1)  = 879
codeM (Sb⁻2-4-01-3) = 880
codeM (Sb⁻2-4-10-3) = 881
codeM (Sb⁻3-0-41-2) = 882
codeM (Sb⁻3-0-42-1) = 883
codeM (Sb⁻3-1-0-4)  = 884
codeM (Sb⁻3-1-4-0)  = 885
codeM (Sb⁻4-0-23-1) = 886
codeM (Sb⁻4-0-31-2) = 887
codeM (Sb⁻4-0-32-1) = 888
codeM (Sb⁻4-1-2-0)  = 889
codeM (Sb⁻4-1-23-0) = 890
codeM (Sb⁻4-1-3-0)  = 891
codeM (Sb⁻4-1-32-0) = 892

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
  (Bx1-04) ∷
  (Bx0-124) ∷
  (Bx0-13) ∷
  (Bx1-043) ∷
  (Bx0-1243) ∷
  (Bx1-02) ∷
  (Bx0-132) ∷
  (Bx1-024) ∷
  (Bx0-1324) ∷
  (Bx0-134) ∷
  (Bx1-042) ∷
  (Bx0-1342) ∷
  (Bx0-142) ∷
  (Bx1-023) ∷
  (Bx0-1423) ∷
  (Bx0-143) ∷
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
  (Bx0-432) ∷
  (Bx4-021) ∷
  (Bx0-4321) ∷
  (Bx1-0234) ∷
  (Bx1-0243) ∷
  (Bx1-0324) ∷
  (Bx1-0342) ∷
  (Bx1-0423) ∷
  (Bx1-0432) ∷
  (Bx1-20) ∷
  (Bx2-13) ∷
  (Bx1-203) ∷
  (Bx1-24) ∷
  (Bx2-134) ∷
  (Bx1-2034) ∷
  (Bx2-14) ∷
  (Bx1-204) ∷
  (Bx1-23) ∷
  (Bx2-143) ∷
  (Bx1-2043) ∷
  (Bx2-10) ∷
  (Bx1-230) ∷
  (Bx2-104) ∷
  (Bx1-2304) ∷
  (Bx1-234) ∷
  (Bx2-140) ∷
  (Bx1-2340) ∷
  (Bx1-240) ∷
  (Bx2-103) ∷
  (Bx1-2403) ∷
  (Bx1-243) ∷
  (Bx2-130) ∷
  (Bx1-2430) ∷
  (Bx1-30) ∷
  (Bx3-12) ∷
  (Bx1-302) ∷
  (Bx1-34) ∷
  (Bx3-124) ∷
  (Bx1-3024) ∷
  (Bx3-14) ∷
  (Bx1-304) ∷
  (Bx1-32) ∷
  (Bx3-142) ∷
  (Bx1-3042) ∷
  (Bx3-10) ∷
  (Bx1-320) ∷
  (Bx3-104) ∷
  (Bx1-3204) ∷
  (Bx1-324) ∷
  (Bx3-140) ∷
  (Bx1-3240) ∷
  (Bx1-340) ∷
  (Bx3-102) ∷
  (Bx1-3402) ∷
  (Bx1-342) ∷
  (Bx3-120) ∷
  (Bx1-3420) ∷
  (Bx1-40) ∷
  (Bx4-12) ∷
  (Bx1-402) ∷
  (Bx1-43) ∷
  (Bx4-123) ∷
  (Bx1-4023) ∷
  (Bx4-13) ∷
  (Bx1-403) ∷
  (Bx1-42) ∷
  (Bx4-132) ∷
  (Bx1-4032) ∷
  (Bx4-10) ∷
  (Bx1-420) ∷
  (Bx4-103) ∷
  (Bx1-4203) ∷
  (Bx1-423) ∷
  (Bx4-130) ∷
  (Bx1-4230) ∷
  (Bx1-430) ∷
  (Bx4-102) ∷
  (Bx1-4302) ∷
  (Bx1-432) ∷
  (Bx4-120) ∷
  (Bx1-4320) ∷
  (Bx2-0134) ∷
  (Bx2-0143) ∷
  (Bx2-0314) ∷
  (Bx2-0341) ∷
  (Bx2-0413) ∷
  (Bx2-0431) ∷
  (Bx2-1034) ∷
  (Bx2-1043) ∷
  (Bx2-1304) ∷
  (Bx2-1340) ∷
  (Bx2-1403) ∷
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
  (Bx2-413) ∷
  (Bx4-230) ∷
  (Bx2-4130) ∷
  (Bx2-430) ∷
  (Bx4-201) ∷
  (Bx2-4301) ∷
  (Bx2-431) ∷
  (Bx4-210) ∷
  (Bx2-4310) ∷
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
  (Bx4-302) ∷
  (Bx3-4102) ∷
  (Bx3-412) ∷
  (Bx4-320) ∷
  (Bx3-4120) ∷
  (Bx4-30) ∷
  (Bx3-420) ∷
  (Bx4-301) ∷
  (Bx3-4201) ∷
  (Bx4-31) ∷
  (Bx3-421) ∷
  (Bx4-310) ∷
  (Bx3-4210) ∷
  (Bx4-0123) ∷
  (Bx4-0132) ∷
  (Bx4-0213) ∷
  (Bx4-0231) ∷
  (Bx4-0312) ∷
  (Bx4-0321) ∷
  (Bx4-1023) ∷
  (Bx4-1032) ∷
  (Bx4-1203) ∷
  (Bx4-1230) ∷
  (Bx4-1302) ∷
  (Bx4-1320) ∷
  (Bx4-2013) ∷
  (Bx4-2031) ∷
  (Bx4-2103) ∷
  (Bx4-2130) ∷
  (Bx4-2301) ∷
  (Bx4-2310) ∷
  (Bx4-3012) ∷
  (Bx4-3021) ∷
  (Bx4-3102) ∷
  (Bx4-3120) ∷
  (Bx⁻0-12) ∷
  (Bx⁻1-03) ∷
  (Bx⁻0-123) ∷
  (Bx⁻0-14) ∷
  (Bx⁻1-034) ∷
  (Bx⁻0-1234) ∷
  (Bx⁻1-04) ∷
  (Bx⁻0-124) ∷
  (Bx⁻0-13) ∷
  (Bx⁻1-043) ∷
  (Bx⁻0-1243) ∷
  (Bx⁻1-02) ∷
  (Bx⁻0-132) ∷
  (Bx⁻1-024) ∷
  (Bx⁻0-1324) ∷
  (Bx⁻0-134) ∷
  (Bx⁻1-042) ∷
  (Bx⁻0-1342) ∷
  (Bx⁻0-142) ∷
  (Bx⁻1-023) ∷
  (Bx⁻0-1423) ∷
  (Bx⁻0-143) ∷
  (Bx⁻1-032) ∷
  (Bx⁻0-1432) ∷
  (Bx⁻0-21) ∷
  (Bx⁻2-03) ∷
  (Bx⁻0-213) ∷
  (Bx⁻0-24) ∷
  (Bx⁻2-034) ∷
  (Bx⁻0-2134) ∷
  (Bx⁻2-04) ∷
  (Bx⁻0-214) ∷
  (Bx⁻2-01) ∷
  (Bx⁻0-231) ∷
  (Bx⁻0-234) ∷
  (Bx⁻2-041) ∷
  (Bx⁻0-2341) ∷
  (Bx⁻0-241) ∷
  (Bx⁻0-243) ∷
  (Bx⁻2-031) ∷
  (Bx⁻0-2431) ∷
  (Bx⁻3-02) ∷
  (Bx⁻0-312) ∷
  (Bx⁻0-34) ∷
  (Bx⁻3-024) ∷
  (Bx⁻0-3124) ∷
  (Bx⁻3-01) ∷
  (Bx⁻0-321) ∷
  (Bx⁻3-04) ∷
  (Bx⁻0-324) ∷
  (Bx⁻4-02) ∷
  (Bx⁻0-412) ∷
  (Bx⁻0-43) ∷
  (Bx⁻4-023) ∷
  (Bx⁻0-4123) ∷
  (Bx⁻4-03) ∷
  (Bx⁻0-413) ∷
  (Bx⁻4-01) ∷
  (Bx⁻0-421) ∷
  (Bx⁻0-423) ∷
  (Bx⁻0-431) ∷
  (Bx⁻0-432) ∷
  (Bx⁻1-0234) ∷
  (Bx⁻1-0243) ∷
  (Bx⁻1-0324) ∷
  (Bx⁻1-0342) ∷
  (Bx⁻1-0423) ∷
  (Bx⁻1-0432) ∷
  (Bx⁻1-20) ∷
  (Bx⁻2-13) ∷
  (Bx⁻1-203) ∷
  (Bx⁻1-24) ∷
  (Bx⁻2-134) ∷
  (Bx⁻1-2034) ∷
  (Bx⁻1-23) ∷
  (Bx⁻2-140) ∷
  (Bx⁻1-2340) ∷
  (Bx⁻2-10) ∷
  (Bx⁻1-240) ∷
  (Bx⁻2-103) ∷
  (Bx⁻1-2403) ∷
  (Bx⁻1-34) ∷
  (Bx⁻3-124) ∷
  (Bx⁻1-3024) ∷
  (Bx⁻1-32) ∷
  (Bx⁻3-102) ∷
  (Bx⁻1-3402) ∷
  (Bx⁻1-43) ∷
  (Bx⁻4-123) ∷
  (Bx⁻1-4023) ∷
  (Bx⁻1-42) ∷
  (Bx⁻4-10) ∷
  (Bx⁻1-420) ∷
  (Bx⁻4-103) ∷
  (Bx⁻1-4203) ∷
  (Bx⁻1-430) ∷
  (Bx⁻4-102) ∷
  (Bx⁻1-4302) ∷
  (Bx⁻2-0134) ∷
  (Bx⁻2-0143) ∷
  (Bx⁻2-0314) ∷
  (Bx⁻2-0341) ∷
  (Bx⁻2-0413) ∷
  (Bx⁻2-0431) ∷
  (Bx⁻2-1340) ∷
  (Bx⁻2-1403) ∷
  (Bx⁻2-34) ∷
  (Bx⁻3-214) ∷
  (Bx⁻2-3014) ∷
  (Bx⁻2-43) ∷
  (Bx⁻4-213) ∷
  (Bx⁻2-4013) ∷
  (Bx⁻4-203) ∷
  (Bx⁻2-4103) ∷
  (Bx⁻3-0124) ∷
  (Bx⁻3-0412) ∷
  (Bx⁻3-0421) ∷
  (Bx⁻4-0123) ∷
  (Bx⁻4-0132) ∷
  (Bx⁻4-0213) ∷
  (Bx⁻4-0231) ∷
  (Bx⁻4-0312) ∷
  (Bx⁻4-0321) ∷
  (Bx⁻4-1230) ∷
  (Bx⁻4-1320) ∷
  (Sb0-1-2-3) ∷
  (Sb0-1-2-4) ∷
  (Sb0-1-4-3) ∷
  (Sb⁻0-1-4-3) ∷
  (Sb0-1-23-4) ∷
  (Sb0-1-3-2) ∷
  (Sb0-1-3-4) ∷
  (Sb0-1-4-2) ∷
  (Sb⁻0-1-4-2) ∷
  (Sb0-1-32-4) ∷
  (Sb⁻0-1-2-4) ∷
  (Sb0-1-34-2) ∷
  (Sb⁻0-1-3-2) ∷
  (Sb0-1-42-3) ∷
  (Sb⁻0-1-2-3) ∷
  (Sb0-1-43-2) ∷
  (Sb0-2-1-3) ∷
  (Sb0-2-1-4) ∷
  (Sb0-2-4-3) ∷
  (Sb⁻0-2-4-3) ∷
  (Sb0-2-13-4) ∷
  (Sb0-2-3-1) ∷
  (Sb0-2-4-1) ∷
  (Sb⁻0-2-4-1) ∷
  (Sb0-2-31-4) ∷
  (Sb⁻0-2-1-4) ∷
  (Sb0-2-34-1) ∷
  (Sb⁻0-2-3-1) ∷
  (Sb0-2-41-3) ∷
  (Sb⁻0-2-1-3) ∷
  (Sb0-2-43-1) ∷
  (Sb0-3-1-2) ∷
  (Sb0-3-1-4) ∷
  (Sb0-3-4-2) ∷
  (Sb⁻0-3-4-2) ∷
  (Sb0-3-12-4) ∷
  (Sb0-3-2-4) ∷
  (Sb⁻0-3-2-4) ∷
  (Sb0-3-14-2) ∷
  (Sb0-3-2-1) ∷
  (Sb0-3-4-1) ∷
  (Sb⁻0-3-4-1) ∷
  (Sb0-3-21-4) ∷
  (Sb⁻0-3-1-4) ∷
  (Sb0-3-24-1) ∷
  (Sb0-4-1-2) ∷
  (Sb0-4-1-3) ∷
  (Sb0-4-3-2) ∷
  (Sb⁻0-4-3-2) ∷
  (Sb0-4-12-3) ∷
  (Sb0-4-2-1) ∷
  (Sb0-4-3-1) ∷
  (Sb⁻0-4-3-1) ∷
  (Sb0-4-21-3) ∷
  (Sb1-0-2-3) ∷
  (Sb1-0-2-4) ∷
  (Sb1-0-4-3) ∷
  (Sb⁻1-0-4-3) ∷
  (Sb1-0-23-4) ∷
  (Sb1-0-3-4) ∷
  (Sb⁻1-0-3-4) ∷
  (Sb1-0-24-3) ∷
  (Sb1-0-3-2) ∷
  (Sb1-0-4-2) ∷
  (Sb⁻1-0-4-2) ∷
  (Sb1-0-32-4) ∷
  (Sb⁻1-0-2-4) ∷
  (Sb1-0-34-2) ∷
  (Sb⁻1-0-3-2) ∷
  (Sb1-0-42-3) ∷
  (Sb⁻1-0-2-3) ∷
  (Sb1-0-43-2) ∷
  (Sb1-2-0-3) ∷
  (Sb1-2-0-4) ∷
  (Sb1-2-4-3) ∷
  (Sb⁻1-2-4-3) ∷
  (Sb1-2-03-4) ∷
  (Sb1-2-3-4) ∷
  (Sb⁻1-2-3-4) ∷
  (Sb1-2-04-3) ∷
  (Sb1-2-3-0) ∷
  (Sb⁻1-2-0-4) ∷
  (Sb1-2-34-0) ∷
  (Sb1-2-4-0) ∷
  (Sb⁻1-2-3-0) ∷
  (Sb1-2-40-3) ∷
  (Sb⁻1-2-0-3) ∷
  (Sb1-2-43-0) ∷
  (Sb1-3-0-4) ∷
  (Sb1-3-2-4) ∷
  (Sb⁻1-3-2-4) ∷
  (Sb1-3-04-2) ∷
  (Sb1-3-2-0) ∷
  (Sb⁻1-3-0-4) ∷
  (Sb1-3-24-0) ∷
  (Sb1-3-4-0) ∷
  (Sb⁻1-3-2-0) ∷
  (Sb1-3-40-2) ∷
  (Sb1-4-2-0) ∷
  (Sb1-4-3-0) ∷
  (Sb⁻1-4-3-0) ∷
  (Sb1-4-20-3) ∷
  (Sb⁻1-4-2-0) ∷
  (Sb1-4-30-2) ∷
  (Sb2-0-1-3) ∷
  (Sb2-0-1-4) ∷
  (Sb2-0-4-3) ∷
  (Sb⁻2-0-4-3) ∷
  (Sb2-0-13-4) ∷
  (Sb2-0-3-4) ∷
  (Sb⁻2-0-3-4) ∷
  (Sb2-0-14-3) ∷
  (Sb2-0-3-1) ∷
  (Sb2-0-4-1) ∷
  (Sb⁻2-0-4-1) ∷
  (Sb2-0-31-4) ∷
  (Sb⁻2-0-1-4) ∷
  (Sb2-0-34-1) ∷
  (Sb⁻2-0-3-1) ∷
  (Sb2-0-41-3) ∷
  (Sb⁻2-0-1-3) ∷
  (Sb2-0-43-1) ∷
  (Sb2-1-0-3) ∷
  (Sb2-1-0-4) ∷
  (Sb2-1-3-0) ∷
  (Sb⁻2-1-0-4) ∷
  (Sb2-1-34-0) ∷
  (Sb2-1-4-0) ∷
  (Sb⁻2-1-3-0) ∷
  (Sb2-1-40-3) ∷
  (Sb⁻2-1-0-3) ∷
  (Sb2-1-43-0) ∷
  (Sb2-3-0-1) ∷
  (Sb2-3-0-4) ∷
  (Sb2-3-1-4) ∷
  (Sb⁻2-3-1-4) ∷
  (Sb2-3-04-1) ∷
  (Sb2-3-1-0) ∷
  (Sb⁻2-3-0-4) ∷
  (Sb2-3-14-0) ∷
  (Sb⁻2-3-1-0) ∷
  (Sb2-3-40-1) ∷
  (Sb⁻2-3-0-1) ∷
  (Sb2-3-41-0) ∷
  (Sb2-4-0-1) ∷
  (Sb2-4-3-1) ∷
  (Sb⁻2-4-3-1) ∷
  (Sb2-4-01-3) ∷
  (Sb2-4-1-0) ∷
  (Sb2-4-3-0) ∷
  (Sb⁻2-4-3-0) ∷
  (Sb2-4-10-3) ∷
  (Sb⁻2-4-1-0) ∷
  (Sb2-4-30-1) ∷
  (Sb⁻2-4-0-1) ∷
  (Sb2-4-31-0) ∷
  (Sb3-0-1-2) ∷
  (Sb3-0-1-4) ∷
  (Sb3-0-2-4) ∷
  (Sb⁻3-0-2-4) ∷
  (Sb3-0-14-2) ∷
  (Sb3-0-2-1) ∷
  (Sb3-0-4-1) ∷
  (Sb⁻3-0-4-1) ∷
  (Sb3-0-21-4) ∷
  (Sb⁻3-0-1-4) ∷
  (Sb3-0-24-1) ∷
  (Sb⁻3-0-2-1) ∷
  (Sb3-0-41-2) ∷
  (Sb⁻3-0-1-2) ∷
  (Sb3-0-42-1) ∷
  (Sb3-1-0-2) ∷
  (Sb3-1-0-4) ∷
  (Sb3-1-2-0) ∷
  (Sb3-1-4-0) ∷
  (Sb⁻3-1-2-0) ∷
  (Sb3-1-40-2) ∷
  (Sb⁻3-1-0-2) ∷
  (Sb3-1-42-0) ∷
  (Sb3-2-0-1) ∷
  (Sb3-2-1-0) ∷
  (Sb⁻3-2-1-0) ∷
  (Sb3-2-40-1) ∷
  (Sb⁻3-2-0-1) ∷
  (Sb3-2-41-0) ∷
  (Sb3-4-0-1) ∷
  (Sb3-4-0-2) ∷
  (Sb3-4-2-1) ∷
  (Sb⁻3-4-2-1) ∷
  (Sb3-4-01-2) ∷
  (Sb3-4-1-0) ∷
  (Sb3-4-2-0) ∷
  (Sb⁻3-4-2-0) ∷
  (Sb3-4-10-2) ∷
  (Sb⁻3-4-0-2) ∷
  (Sb3-4-12-0) ∷
  (Sb⁻3-4-1-0) ∷
  (Sb3-4-20-1) ∷
  (Sb⁻3-4-0-1) ∷
  (Sb3-4-21-0) ∷
  (Sb4-0-1-2) ∷
  (Sb4-0-1-3) ∷
  (Sb4-0-3-2) ∷
  (Sb⁻4-0-3-2) ∷
  (Sb4-0-12-3) ∷
  (Sb4-0-2-3) ∷
  (Sb⁻4-0-2-3) ∷
  (Sb4-0-13-2) ∷
  (Sb4-0-2-1) ∷
  (Sb4-0-3-1) ∷
  (Sb⁻4-0-3-1) ∷
  (Sb4-0-21-3) ∷
  (Sb⁻4-0-1-3) ∷
  (Sb4-0-23-1) ∷
  (Sb⁻4-0-2-1) ∷
  (Sb4-0-31-2) ∷
  (Sb⁻4-0-1-2) ∷
  (Sb4-0-32-1) ∷
  (Sb4-1-0-2) ∷
  (Sb4-1-0-3) ∷
  (Sb4-1-3-2) ∷
  (Sb⁻4-1-3-2) ∷
  (Sb4-1-02-3) ∷
  (Sb4-1-2-3) ∷
  (Sb⁻4-1-2-3) ∷
  (Sb4-1-03-2) ∷
  (Sb4-1-2-0) ∷
  (Sb⁻4-1-0-3) ∷
  (Sb4-1-23-0) ∷
  (Sb4-1-3-0) ∷
  (Sb⁻4-1-0-2) ∷
  (Sb4-1-32-0) ∷
  (Sb4-2-0-3) ∷
  (Sb4-2-1-3) ∷
  (Sb⁻4-2-1-3) ∷
  (Sb4-2-03-1) ∷
  (Sb⁻4-2-0-3) ∷
  (Sb4-2-13-0) ∷
  (Sb4-2-3-0) ∷
  (Sb4-3-1-0) ∷
  (Sb4-3-2-0) ∷
  (Sb⁻0-1-23-4) ∷
  (Sb⁻0-1-3-4) ∷
  (Sb⁻0-1-32-4) ∷
  (Sb⁻0-1-34-2) ∷
  (Sb⁻0-1-42-3) ∷
  (Sb⁻0-1-43-2) ∷
  (Sb⁻0-2-34-1) ∷
  (Sb⁻0-2-43-1) ∷
  (Sb⁻0-3-1-2) ∷
  (Sb⁻0-3-2-1) ∷
  (Sb⁻0-4-1-2) ∷
  (Sb⁻0-4-1-3) ∷
  (Sb⁻0-4-2-1) ∷
  (Sb⁻1-0-23-4) ∷
  (Sb⁻1-0-24-3) ∷
  (Sb⁻1-0-32-4) ∷
  (Sb⁻1-0-34-2) ∷
  (Sb⁻1-0-42-3) ∷
  (Sb⁻1-0-43-2) ∷
  (Sb⁻1-2-34-0) ∷
  (Sb⁻1-2-4-0) ∷
  (Sb⁻1-2-40-3) ∷
  (Sb⁻1-3-4-0) ∷
  (Sb⁻1-3-4-2) ∷
  (Sb⁻1-3-40-2) ∷
  (Sb⁻1-4-20-3) ∷
  (Sb⁻1-4-30-2) ∷
  (Sb⁻2-0-13-4) ∷
  (Sb⁻2-0-14-3) ∷
  (Sb⁻2-0-31-4) ∷
  (Sb⁻2-0-34-1) ∷
  (Sb⁻2-0-41-3) ∷
  (Sb⁻2-0-43-1) ∷
  (Sb⁻2-1-34-0) ∷
  (Sb⁻2-1-4-0) ∷
  (Sb⁻2-1-40-3) ∷
  (Sb⁻2-3-4-0) ∷
  (Sb⁻2-3-4-1) ∷
  (Sb⁻2-4-01-3) ∷
  (Sb⁻2-4-10-3) ∷
  (Sb⁻3-0-41-2) ∷
  (Sb⁻3-0-42-1) ∷
  (Sb⁻3-1-0-4) ∷
  (Sb⁻3-1-4-0) ∷
  (Sb⁻4-0-23-1) ∷
  (Sb⁻4-0-31-2) ∷
  (Sb⁻4-0-32-1) ∷
  (Sb⁻4-1-2-0) ∷
  (Sb⁻4-1-23-0) ∷
  (Sb⁻4-1-3-0) ∷
  (Sb⁻4-1-32-0) ∷
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
decode-codeM (Bx1-04)      = Eq.refl
decode-codeM (Bx0-124)     = Eq.refl
decode-codeM (Bx0-13)      = Eq.refl
decode-codeM (Bx1-043)     = Eq.refl
decode-codeM (Bx0-1243)    = Eq.refl
decode-codeM (Bx1-02)      = Eq.refl
decode-codeM (Bx0-132)     = Eq.refl
decode-codeM (Bx1-024)     = Eq.refl
decode-codeM (Bx0-1324)    = Eq.refl
decode-codeM (Bx0-134)     = Eq.refl
decode-codeM (Bx1-042)     = Eq.refl
decode-codeM (Bx0-1342)    = Eq.refl
decode-codeM (Bx0-142)     = Eq.refl
decode-codeM (Bx1-023)     = Eq.refl
decode-codeM (Bx0-1423)    = Eq.refl
decode-codeM (Bx0-143)     = Eq.refl
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
decode-codeM (Bx0-432)     = Eq.refl
decode-codeM (Bx4-021)     = Eq.refl
decode-codeM (Bx0-4321)    = Eq.refl
decode-codeM (Bx1-0234)    = Eq.refl
decode-codeM (Bx1-0243)    = Eq.refl
decode-codeM (Bx1-0324)    = Eq.refl
decode-codeM (Bx1-0342)    = Eq.refl
decode-codeM (Bx1-0423)    = Eq.refl
decode-codeM (Bx1-0432)    = Eq.refl
decode-codeM (Bx1-20)      = Eq.refl
decode-codeM (Bx2-13)      = Eq.refl
decode-codeM (Bx1-203)     = Eq.refl
decode-codeM (Bx1-24)      = Eq.refl
decode-codeM (Bx2-134)     = Eq.refl
decode-codeM (Bx1-2034)    = Eq.refl
decode-codeM (Bx2-14)      = Eq.refl
decode-codeM (Bx1-204)     = Eq.refl
decode-codeM (Bx1-23)      = Eq.refl
decode-codeM (Bx2-143)     = Eq.refl
decode-codeM (Bx1-2043)    = Eq.refl
decode-codeM (Bx2-10)      = Eq.refl
decode-codeM (Bx1-230)     = Eq.refl
decode-codeM (Bx2-104)     = Eq.refl
decode-codeM (Bx1-2304)    = Eq.refl
decode-codeM (Bx1-234)     = Eq.refl
decode-codeM (Bx2-140)     = Eq.refl
decode-codeM (Bx1-2340)    = Eq.refl
decode-codeM (Bx1-240)     = Eq.refl
decode-codeM (Bx2-103)     = Eq.refl
decode-codeM (Bx1-2403)    = Eq.refl
decode-codeM (Bx1-243)     = Eq.refl
decode-codeM (Bx2-130)     = Eq.refl
decode-codeM (Bx1-2430)    = Eq.refl
decode-codeM (Bx1-30)      = Eq.refl
decode-codeM (Bx3-12)      = Eq.refl
decode-codeM (Bx1-302)     = Eq.refl
decode-codeM (Bx1-34)      = Eq.refl
decode-codeM (Bx3-124)     = Eq.refl
decode-codeM (Bx1-3024)    = Eq.refl
decode-codeM (Bx3-14)      = Eq.refl
decode-codeM (Bx1-304)     = Eq.refl
decode-codeM (Bx1-32)      = Eq.refl
decode-codeM (Bx3-142)     = Eq.refl
decode-codeM (Bx1-3042)    = Eq.refl
decode-codeM (Bx3-10)      = Eq.refl
decode-codeM (Bx1-320)     = Eq.refl
decode-codeM (Bx3-104)     = Eq.refl
decode-codeM (Bx1-3204)    = Eq.refl
decode-codeM (Bx1-324)     = Eq.refl
decode-codeM (Bx3-140)     = Eq.refl
decode-codeM (Bx1-3240)    = Eq.refl
decode-codeM (Bx1-340)     = Eq.refl
decode-codeM (Bx3-102)     = Eq.refl
decode-codeM (Bx1-3402)    = Eq.refl
decode-codeM (Bx1-342)     = Eq.refl
decode-codeM (Bx3-120)     = Eq.refl
decode-codeM (Bx1-3420)    = Eq.refl
decode-codeM (Bx1-40)      = Eq.refl
decode-codeM (Bx4-12)      = Eq.refl
decode-codeM (Bx1-402)     = Eq.refl
decode-codeM (Bx1-43)      = Eq.refl
decode-codeM (Bx4-123)     = Eq.refl
decode-codeM (Bx1-4023)    = Eq.refl
decode-codeM (Bx4-13)      = Eq.refl
decode-codeM (Bx1-403)     = Eq.refl
decode-codeM (Bx1-42)      = Eq.refl
decode-codeM (Bx4-132)     = Eq.refl
decode-codeM (Bx1-4032)    = Eq.refl
decode-codeM (Bx4-10)      = Eq.refl
decode-codeM (Bx1-420)     = Eq.refl
decode-codeM (Bx4-103)     = Eq.refl
decode-codeM (Bx1-4203)    = Eq.refl
decode-codeM (Bx1-423)     = Eq.refl
decode-codeM (Bx4-130)     = Eq.refl
decode-codeM (Bx1-4230)    = Eq.refl
decode-codeM (Bx1-430)     = Eq.refl
decode-codeM (Bx4-102)     = Eq.refl
decode-codeM (Bx1-4302)    = Eq.refl
decode-codeM (Bx1-432)     = Eq.refl
decode-codeM (Bx4-120)     = Eq.refl
decode-codeM (Bx1-4320)    = Eq.refl
decode-codeM (Bx2-0134)    = Eq.refl
decode-codeM (Bx2-0143)    = Eq.refl
decode-codeM (Bx2-0314)    = Eq.refl
decode-codeM (Bx2-0341)    = Eq.refl
decode-codeM (Bx2-0413)    = Eq.refl
decode-codeM (Bx2-0431)    = Eq.refl
decode-codeM (Bx2-1034)    = Eq.refl
decode-codeM (Bx2-1043)    = Eq.refl
decode-codeM (Bx2-1304)    = Eq.refl
decode-codeM (Bx2-1340)    = Eq.refl
decode-codeM (Bx2-1403)    = Eq.refl
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
decode-codeM (Bx2-413)     = Eq.refl
decode-codeM (Bx4-230)     = Eq.refl
decode-codeM (Bx2-4130)    = Eq.refl
decode-codeM (Bx2-430)     = Eq.refl
decode-codeM (Bx4-201)     = Eq.refl
decode-codeM (Bx2-4301)    = Eq.refl
decode-codeM (Bx2-431)     = Eq.refl
decode-codeM (Bx4-210)     = Eq.refl
decode-codeM (Bx2-4310)    = Eq.refl
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
decode-codeM (Bx4-302)     = Eq.refl
decode-codeM (Bx3-4102)    = Eq.refl
decode-codeM (Bx3-412)     = Eq.refl
decode-codeM (Bx4-320)     = Eq.refl
decode-codeM (Bx3-4120)    = Eq.refl
decode-codeM (Bx4-30)      = Eq.refl
decode-codeM (Bx3-420)     = Eq.refl
decode-codeM (Bx4-301)     = Eq.refl
decode-codeM (Bx3-4201)    = Eq.refl
decode-codeM (Bx4-31)      = Eq.refl
decode-codeM (Bx3-421)     = Eq.refl
decode-codeM (Bx4-310)     = Eq.refl
decode-codeM (Bx3-4210)    = Eq.refl
decode-codeM (Bx4-0123)    = Eq.refl
decode-codeM (Bx4-0132)    = Eq.refl
decode-codeM (Bx4-0213)    = Eq.refl
decode-codeM (Bx4-0231)    = Eq.refl
decode-codeM (Bx4-0312)    = Eq.refl
decode-codeM (Bx4-0321)    = Eq.refl
decode-codeM (Bx4-1023)    = Eq.refl
decode-codeM (Bx4-1032)    = Eq.refl
decode-codeM (Bx4-1203)    = Eq.refl
decode-codeM (Bx4-1230)    = Eq.refl
decode-codeM (Bx4-1302)    = Eq.refl
decode-codeM (Bx4-1320)    = Eq.refl
decode-codeM (Bx4-2013)    = Eq.refl
decode-codeM (Bx4-2031)    = Eq.refl
decode-codeM (Bx4-2103)    = Eq.refl
decode-codeM (Bx4-2130)    = Eq.refl
decode-codeM (Bx4-2301)    = Eq.refl
decode-codeM (Bx4-2310)    = Eq.refl
decode-codeM (Bx4-3012)    = Eq.refl
decode-codeM (Bx4-3021)    = Eq.refl
decode-codeM (Bx4-3102)    = Eq.refl
decode-codeM (Bx4-3120)    = Eq.refl
decode-codeM (Bx⁻0-12)     = Eq.refl
decode-codeM (Bx⁻1-03)     = Eq.refl
decode-codeM (Bx⁻0-123)    = Eq.refl
decode-codeM (Bx⁻0-14)     = Eq.refl
decode-codeM (Bx⁻1-034)    = Eq.refl
decode-codeM (Bx⁻0-1234)   = Eq.refl
decode-codeM (Bx⁻1-04)     = Eq.refl
decode-codeM (Bx⁻0-124)    = Eq.refl
decode-codeM (Bx⁻0-13)     = Eq.refl
decode-codeM (Bx⁻1-043)    = Eq.refl
decode-codeM (Bx⁻0-1243)   = Eq.refl
decode-codeM (Bx⁻1-02)     = Eq.refl
decode-codeM (Bx⁻0-132)    = Eq.refl
decode-codeM (Bx⁻1-024)    = Eq.refl
decode-codeM (Bx⁻0-1324)   = Eq.refl
decode-codeM (Bx⁻0-134)    = Eq.refl
decode-codeM (Bx⁻1-042)    = Eq.refl
decode-codeM (Bx⁻0-1342)   = Eq.refl
decode-codeM (Bx⁻0-142)    = Eq.refl
decode-codeM (Bx⁻1-023)    = Eq.refl
decode-codeM (Bx⁻0-1423)   = Eq.refl
decode-codeM (Bx⁻0-143)    = Eq.refl
decode-codeM (Bx⁻1-032)    = Eq.refl
decode-codeM (Bx⁻0-1432)   = Eq.refl
decode-codeM (Bx⁻0-21)     = Eq.refl
decode-codeM (Bx⁻2-03)     = Eq.refl
decode-codeM (Bx⁻0-213)    = Eq.refl
decode-codeM (Bx⁻0-24)     = Eq.refl
decode-codeM (Bx⁻2-034)    = Eq.refl
decode-codeM (Bx⁻0-2134)   = Eq.refl
decode-codeM (Bx⁻2-04)     = Eq.refl
decode-codeM (Bx⁻0-214)    = Eq.refl
decode-codeM (Bx⁻2-01)     = Eq.refl
decode-codeM (Bx⁻0-231)    = Eq.refl
decode-codeM (Bx⁻0-234)    = Eq.refl
decode-codeM (Bx⁻2-041)    = Eq.refl
decode-codeM (Bx⁻0-2341)   = Eq.refl
decode-codeM (Bx⁻0-241)    = Eq.refl
decode-codeM (Bx⁻0-243)    = Eq.refl
decode-codeM (Bx⁻2-031)    = Eq.refl
decode-codeM (Bx⁻0-2431)   = Eq.refl
decode-codeM (Bx⁻3-02)     = Eq.refl
decode-codeM (Bx⁻0-312)    = Eq.refl
decode-codeM (Bx⁻0-34)     = Eq.refl
decode-codeM (Bx⁻3-024)    = Eq.refl
decode-codeM (Bx⁻0-3124)   = Eq.refl
decode-codeM (Bx⁻3-01)     = Eq.refl
decode-codeM (Bx⁻0-321)    = Eq.refl
decode-codeM (Bx⁻3-04)     = Eq.refl
decode-codeM (Bx⁻0-324)    = Eq.refl
decode-codeM (Bx⁻4-02)     = Eq.refl
decode-codeM (Bx⁻0-412)    = Eq.refl
decode-codeM (Bx⁻0-43)     = Eq.refl
decode-codeM (Bx⁻4-023)    = Eq.refl
decode-codeM (Bx⁻0-4123)   = Eq.refl
decode-codeM (Bx⁻4-03)     = Eq.refl
decode-codeM (Bx⁻0-413)    = Eq.refl
decode-codeM (Bx⁻4-01)     = Eq.refl
decode-codeM (Bx⁻0-421)    = Eq.refl
decode-codeM (Bx⁻0-423)    = Eq.refl
decode-codeM (Bx⁻0-431)    = Eq.refl
decode-codeM (Bx⁻0-432)    = Eq.refl
decode-codeM (Bx⁻1-0234)   = Eq.refl
decode-codeM (Bx⁻1-0243)   = Eq.refl
decode-codeM (Bx⁻1-0324)   = Eq.refl
decode-codeM (Bx⁻1-0342)   = Eq.refl
decode-codeM (Bx⁻1-0423)   = Eq.refl
decode-codeM (Bx⁻1-0432)   = Eq.refl
decode-codeM (Bx⁻1-20)     = Eq.refl
decode-codeM (Bx⁻2-13)     = Eq.refl
decode-codeM (Bx⁻1-203)    = Eq.refl
decode-codeM (Bx⁻1-24)     = Eq.refl
decode-codeM (Bx⁻2-134)    = Eq.refl
decode-codeM (Bx⁻1-2034)   = Eq.refl
decode-codeM (Bx⁻1-23)     = Eq.refl
decode-codeM (Bx⁻2-140)    = Eq.refl
decode-codeM (Bx⁻1-2340)   = Eq.refl
decode-codeM (Bx⁻2-10)     = Eq.refl
decode-codeM (Bx⁻1-240)    = Eq.refl
decode-codeM (Bx⁻2-103)    = Eq.refl
decode-codeM (Bx⁻1-2403)   = Eq.refl
decode-codeM (Bx⁻1-34)     = Eq.refl
decode-codeM (Bx⁻3-124)    = Eq.refl
decode-codeM (Bx⁻1-3024)   = Eq.refl
decode-codeM (Bx⁻1-32)     = Eq.refl
decode-codeM (Bx⁻3-102)    = Eq.refl
decode-codeM (Bx⁻1-3402)   = Eq.refl
decode-codeM (Bx⁻1-43)     = Eq.refl
decode-codeM (Bx⁻4-123)    = Eq.refl
decode-codeM (Bx⁻1-4023)   = Eq.refl
decode-codeM (Bx⁻1-42)     = Eq.refl
decode-codeM (Bx⁻4-10)     = Eq.refl
decode-codeM (Bx⁻1-420)    = Eq.refl
decode-codeM (Bx⁻4-103)    = Eq.refl
decode-codeM (Bx⁻1-4203)   = Eq.refl
decode-codeM (Bx⁻1-430)    = Eq.refl
decode-codeM (Bx⁻4-102)    = Eq.refl
decode-codeM (Bx⁻1-4302)   = Eq.refl
decode-codeM (Bx⁻2-0134)   = Eq.refl
decode-codeM (Bx⁻2-0143)   = Eq.refl
decode-codeM (Bx⁻2-0314)   = Eq.refl
decode-codeM (Bx⁻2-0341)   = Eq.refl
decode-codeM (Bx⁻2-0413)   = Eq.refl
decode-codeM (Bx⁻2-0431)   = Eq.refl
decode-codeM (Bx⁻2-1340)   = Eq.refl
decode-codeM (Bx⁻2-1403)   = Eq.refl
decode-codeM (Bx⁻2-34)     = Eq.refl
decode-codeM (Bx⁻3-214)    = Eq.refl
decode-codeM (Bx⁻2-3014)   = Eq.refl
decode-codeM (Bx⁻2-43)     = Eq.refl
decode-codeM (Bx⁻4-213)    = Eq.refl
decode-codeM (Bx⁻2-4013)   = Eq.refl
decode-codeM (Bx⁻4-203)    = Eq.refl
decode-codeM (Bx⁻2-4103)   = Eq.refl
decode-codeM (Bx⁻3-0124)   = Eq.refl
decode-codeM (Bx⁻3-0412)   = Eq.refl
decode-codeM (Bx⁻3-0421)   = Eq.refl
decode-codeM (Bx⁻4-0123)   = Eq.refl
decode-codeM (Bx⁻4-0132)   = Eq.refl
decode-codeM (Bx⁻4-0213)   = Eq.refl
decode-codeM (Bx⁻4-0231)   = Eq.refl
decode-codeM (Bx⁻4-0312)   = Eq.refl
decode-codeM (Bx⁻4-0321)   = Eq.refl
decode-codeM (Bx⁻4-1230)   = Eq.refl
decode-codeM (Bx⁻4-1320)   = Eq.refl
decode-codeM (Sb0-1-2-3)   = Eq.refl
decode-codeM (Sb0-1-2-4)   = Eq.refl
decode-codeM (Sb0-1-4-3)   = Eq.refl
decode-codeM (Sb⁻0-1-4-3)  = Eq.refl
decode-codeM (Sb0-1-23-4)  = Eq.refl
decode-codeM (Sb0-1-3-2)   = Eq.refl
decode-codeM (Sb0-1-3-4)   = Eq.refl
decode-codeM (Sb0-1-4-2)   = Eq.refl
decode-codeM (Sb⁻0-1-4-2)  = Eq.refl
decode-codeM (Sb0-1-32-4)  = Eq.refl
decode-codeM (Sb⁻0-1-2-4)  = Eq.refl
decode-codeM (Sb0-1-34-2)  = Eq.refl
decode-codeM (Sb⁻0-1-3-2)  = Eq.refl
decode-codeM (Sb0-1-42-3)  = Eq.refl
decode-codeM (Sb⁻0-1-2-3)  = Eq.refl
decode-codeM (Sb0-1-43-2)  = Eq.refl
decode-codeM (Sb0-2-1-3)   = Eq.refl
decode-codeM (Sb0-2-1-4)   = Eq.refl
decode-codeM (Sb0-2-4-3)   = Eq.refl
decode-codeM (Sb⁻0-2-4-3)  = Eq.refl
decode-codeM (Sb0-2-13-4)  = Eq.refl
decode-codeM (Sb0-2-3-1)   = Eq.refl
decode-codeM (Sb0-2-4-1)   = Eq.refl
decode-codeM (Sb⁻0-2-4-1)  = Eq.refl
decode-codeM (Sb0-2-31-4)  = Eq.refl
decode-codeM (Sb⁻0-2-1-4)  = Eq.refl
decode-codeM (Sb0-2-34-1)  = Eq.refl
decode-codeM (Sb⁻0-2-3-1)  = Eq.refl
decode-codeM (Sb0-2-41-3)  = Eq.refl
decode-codeM (Sb⁻0-2-1-3)  = Eq.refl
decode-codeM (Sb0-2-43-1)  = Eq.refl
decode-codeM (Sb0-3-1-2)   = Eq.refl
decode-codeM (Sb0-3-1-4)   = Eq.refl
decode-codeM (Sb0-3-4-2)   = Eq.refl
decode-codeM (Sb⁻0-3-4-2)  = Eq.refl
decode-codeM (Sb0-3-12-4)  = Eq.refl
decode-codeM (Sb0-3-2-4)   = Eq.refl
decode-codeM (Sb⁻0-3-2-4)  = Eq.refl
decode-codeM (Sb0-3-14-2)  = Eq.refl
decode-codeM (Sb0-3-2-1)   = Eq.refl
decode-codeM (Sb0-3-4-1)   = Eq.refl
decode-codeM (Sb⁻0-3-4-1)  = Eq.refl
decode-codeM (Sb0-3-21-4)  = Eq.refl
decode-codeM (Sb⁻0-3-1-4)  = Eq.refl
decode-codeM (Sb0-3-24-1)  = Eq.refl
decode-codeM (Sb0-4-1-2)   = Eq.refl
decode-codeM (Sb0-4-1-3)   = Eq.refl
decode-codeM (Sb0-4-3-2)   = Eq.refl
decode-codeM (Sb⁻0-4-3-2)  = Eq.refl
decode-codeM (Sb0-4-12-3)  = Eq.refl
decode-codeM (Sb0-4-2-1)   = Eq.refl
decode-codeM (Sb0-4-3-1)   = Eq.refl
decode-codeM (Sb⁻0-4-3-1)  = Eq.refl
decode-codeM (Sb0-4-21-3)  = Eq.refl
decode-codeM (Sb1-0-2-3)   = Eq.refl
decode-codeM (Sb1-0-2-4)   = Eq.refl
decode-codeM (Sb1-0-4-3)   = Eq.refl
decode-codeM (Sb⁻1-0-4-3)  = Eq.refl
decode-codeM (Sb1-0-23-4)  = Eq.refl
decode-codeM (Sb1-0-3-4)   = Eq.refl
decode-codeM (Sb⁻1-0-3-4)  = Eq.refl
decode-codeM (Sb1-0-24-3)  = Eq.refl
decode-codeM (Sb1-0-3-2)   = Eq.refl
decode-codeM (Sb1-0-4-2)   = Eq.refl
decode-codeM (Sb⁻1-0-4-2)  = Eq.refl
decode-codeM (Sb1-0-32-4)  = Eq.refl
decode-codeM (Sb⁻1-0-2-4)  = Eq.refl
decode-codeM (Sb1-0-34-2)  = Eq.refl
decode-codeM (Sb⁻1-0-3-2)  = Eq.refl
decode-codeM (Sb1-0-42-3)  = Eq.refl
decode-codeM (Sb⁻1-0-2-3)  = Eq.refl
decode-codeM (Sb1-0-43-2)  = Eq.refl
decode-codeM (Sb1-2-0-3)   = Eq.refl
decode-codeM (Sb1-2-0-4)   = Eq.refl
decode-codeM (Sb1-2-4-3)   = Eq.refl
decode-codeM (Sb⁻1-2-4-3)  = Eq.refl
decode-codeM (Sb1-2-03-4)  = Eq.refl
decode-codeM (Sb1-2-3-4)   = Eq.refl
decode-codeM (Sb⁻1-2-3-4)  = Eq.refl
decode-codeM (Sb1-2-04-3)  = Eq.refl
decode-codeM (Sb1-2-3-0)   = Eq.refl
decode-codeM (Sb⁻1-2-0-4)  = Eq.refl
decode-codeM (Sb1-2-34-0)  = Eq.refl
decode-codeM (Sb1-2-4-0)   = Eq.refl
decode-codeM (Sb⁻1-2-3-0)  = Eq.refl
decode-codeM (Sb1-2-40-3)  = Eq.refl
decode-codeM (Sb⁻1-2-0-3)  = Eq.refl
decode-codeM (Sb1-2-43-0)  = Eq.refl
decode-codeM (Sb1-3-0-4)   = Eq.refl
decode-codeM (Sb1-3-2-4)   = Eq.refl
decode-codeM (Sb⁻1-3-2-4)  = Eq.refl
decode-codeM (Sb1-3-04-2)  = Eq.refl
decode-codeM (Sb1-3-2-0)   = Eq.refl
decode-codeM (Sb⁻1-3-0-4)  = Eq.refl
decode-codeM (Sb1-3-24-0)  = Eq.refl
decode-codeM (Sb1-3-4-0)   = Eq.refl
decode-codeM (Sb⁻1-3-2-0)  = Eq.refl
decode-codeM (Sb1-3-40-2)  = Eq.refl
decode-codeM (Sb1-4-2-0)   = Eq.refl
decode-codeM (Sb1-4-3-0)   = Eq.refl
decode-codeM (Sb⁻1-4-3-0)  = Eq.refl
decode-codeM (Sb1-4-20-3)  = Eq.refl
decode-codeM (Sb⁻1-4-2-0)  = Eq.refl
decode-codeM (Sb1-4-30-2)  = Eq.refl
decode-codeM (Sb2-0-1-3)   = Eq.refl
decode-codeM (Sb2-0-1-4)   = Eq.refl
decode-codeM (Sb2-0-4-3)   = Eq.refl
decode-codeM (Sb⁻2-0-4-3)  = Eq.refl
decode-codeM (Sb2-0-13-4)  = Eq.refl
decode-codeM (Sb2-0-3-4)   = Eq.refl
decode-codeM (Sb⁻2-0-3-4)  = Eq.refl
decode-codeM (Sb2-0-14-3)  = Eq.refl
decode-codeM (Sb2-0-3-1)   = Eq.refl
decode-codeM (Sb2-0-4-1)   = Eq.refl
decode-codeM (Sb⁻2-0-4-1)  = Eq.refl
decode-codeM (Sb2-0-31-4)  = Eq.refl
decode-codeM (Sb⁻2-0-1-4)  = Eq.refl
decode-codeM (Sb2-0-34-1)  = Eq.refl
decode-codeM (Sb⁻2-0-3-1)  = Eq.refl
decode-codeM (Sb2-0-41-3)  = Eq.refl
decode-codeM (Sb⁻2-0-1-3)  = Eq.refl
decode-codeM (Sb2-0-43-1)  = Eq.refl
decode-codeM (Sb2-1-0-3)   = Eq.refl
decode-codeM (Sb2-1-0-4)   = Eq.refl
decode-codeM (Sb2-1-3-0)   = Eq.refl
decode-codeM (Sb⁻2-1-0-4)  = Eq.refl
decode-codeM (Sb2-1-34-0)  = Eq.refl
decode-codeM (Sb2-1-4-0)   = Eq.refl
decode-codeM (Sb⁻2-1-3-0)  = Eq.refl
decode-codeM (Sb2-1-40-3)  = Eq.refl
decode-codeM (Sb⁻2-1-0-3)  = Eq.refl
decode-codeM (Sb2-1-43-0)  = Eq.refl
decode-codeM (Sb2-3-0-1)   = Eq.refl
decode-codeM (Sb2-3-0-4)   = Eq.refl
decode-codeM (Sb2-3-1-4)   = Eq.refl
decode-codeM (Sb⁻2-3-1-4)  = Eq.refl
decode-codeM (Sb2-3-04-1)  = Eq.refl
decode-codeM (Sb2-3-1-0)   = Eq.refl
decode-codeM (Sb⁻2-3-0-4)  = Eq.refl
decode-codeM (Sb2-3-14-0)  = Eq.refl
decode-codeM (Sb⁻2-3-1-0)  = Eq.refl
decode-codeM (Sb2-3-40-1)  = Eq.refl
decode-codeM (Sb⁻2-3-0-1)  = Eq.refl
decode-codeM (Sb2-3-41-0)  = Eq.refl
decode-codeM (Sb2-4-0-1)   = Eq.refl
decode-codeM (Sb2-4-3-1)   = Eq.refl
decode-codeM (Sb⁻2-4-3-1)  = Eq.refl
decode-codeM (Sb2-4-01-3)  = Eq.refl
decode-codeM (Sb2-4-1-0)   = Eq.refl
decode-codeM (Sb2-4-3-0)   = Eq.refl
decode-codeM (Sb⁻2-4-3-0)  = Eq.refl
decode-codeM (Sb2-4-10-3)  = Eq.refl
decode-codeM (Sb⁻2-4-1-0)  = Eq.refl
decode-codeM (Sb2-4-30-1)  = Eq.refl
decode-codeM (Sb⁻2-4-0-1)  = Eq.refl
decode-codeM (Sb2-4-31-0)  = Eq.refl
decode-codeM (Sb3-0-1-2)   = Eq.refl
decode-codeM (Sb3-0-1-4)   = Eq.refl
decode-codeM (Sb3-0-2-4)   = Eq.refl
decode-codeM (Sb⁻3-0-2-4)  = Eq.refl
decode-codeM (Sb3-0-14-2)  = Eq.refl
decode-codeM (Sb3-0-2-1)   = Eq.refl
decode-codeM (Sb3-0-4-1)   = Eq.refl
decode-codeM (Sb⁻3-0-4-1)  = Eq.refl
decode-codeM (Sb3-0-21-4)  = Eq.refl
decode-codeM (Sb⁻3-0-1-4)  = Eq.refl
decode-codeM (Sb3-0-24-1)  = Eq.refl
decode-codeM (Sb⁻3-0-2-1)  = Eq.refl
decode-codeM (Sb3-0-41-2)  = Eq.refl
decode-codeM (Sb⁻3-0-1-2)  = Eq.refl
decode-codeM (Sb3-0-42-1)  = Eq.refl
decode-codeM (Sb3-1-0-2)   = Eq.refl
decode-codeM (Sb3-1-0-4)   = Eq.refl
decode-codeM (Sb3-1-2-0)   = Eq.refl
decode-codeM (Sb3-1-4-0)   = Eq.refl
decode-codeM (Sb⁻3-1-2-0)  = Eq.refl
decode-codeM (Sb3-1-40-2)  = Eq.refl
decode-codeM (Sb⁻3-1-0-2)  = Eq.refl
decode-codeM (Sb3-1-42-0)  = Eq.refl
decode-codeM (Sb3-2-0-1)   = Eq.refl
decode-codeM (Sb3-2-1-0)   = Eq.refl
decode-codeM (Sb⁻3-2-1-0)  = Eq.refl
decode-codeM (Sb3-2-40-1)  = Eq.refl
decode-codeM (Sb⁻3-2-0-1)  = Eq.refl
decode-codeM (Sb3-2-41-0)  = Eq.refl
decode-codeM (Sb3-4-0-1)   = Eq.refl
decode-codeM (Sb3-4-0-2)   = Eq.refl
decode-codeM (Sb3-4-2-1)   = Eq.refl
decode-codeM (Sb⁻3-4-2-1)  = Eq.refl
decode-codeM (Sb3-4-01-2)  = Eq.refl
decode-codeM (Sb3-4-1-0)   = Eq.refl
decode-codeM (Sb3-4-2-0)   = Eq.refl
decode-codeM (Sb⁻3-4-2-0)  = Eq.refl
decode-codeM (Sb3-4-10-2)  = Eq.refl
decode-codeM (Sb⁻3-4-0-2)  = Eq.refl
decode-codeM (Sb3-4-12-0)  = Eq.refl
decode-codeM (Sb⁻3-4-1-0)  = Eq.refl
decode-codeM (Sb3-4-20-1)  = Eq.refl
decode-codeM (Sb⁻3-4-0-1)  = Eq.refl
decode-codeM (Sb3-4-21-0)  = Eq.refl
decode-codeM (Sb4-0-1-2)   = Eq.refl
decode-codeM (Sb4-0-1-3)   = Eq.refl
decode-codeM (Sb4-0-3-2)   = Eq.refl
decode-codeM (Sb⁻4-0-3-2)  = Eq.refl
decode-codeM (Sb4-0-12-3)  = Eq.refl
decode-codeM (Sb4-0-2-3)   = Eq.refl
decode-codeM (Sb⁻4-0-2-3)  = Eq.refl
decode-codeM (Sb4-0-13-2)  = Eq.refl
decode-codeM (Sb4-0-2-1)   = Eq.refl
decode-codeM (Sb4-0-3-1)   = Eq.refl
decode-codeM (Sb⁻4-0-3-1)  = Eq.refl
decode-codeM (Sb4-0-21-3)  = Eq.refl
decode-codeM (Sb⁻4-0-1-3)  = Eq.refl
decode-codeM (Sb4-0-23-1)  = Eq.refl
decode-codeM (Sb⁻4-0-2-1)  = Eq.refl
decode-codeM (Sb4-0-31-2)  = Eq.refl
decode-codeM (Sb⁻4-0-1-2)  = Eq.refl
decode-codeM (Sb4-0-32-1)  = Eq.refl
decode-codeM (Sb4-1-0-2)   = Eq.refl
decode-codeM (Sb4-1-0-3)   = Eq.refl
decode-codeM (Sb4-1-3-2)   = Eq.refl
decode-codeM (Sb⁻4-1-3-2)  = Eq.refl
decode-codeM (Sb4-1-02-3)  = Eq.refl
decode-codeM (Sb4-1-2-3)   = Eq.refl
decode-codeM (Sb⁻4-1-2-3)  = Eq.refl
decode-codeM (Sb4-1-03-2)  = Eq.refl
decode-codeM (Sb4-1-2-0)   = Eq.refl
decode-codeM (Sb⁻4-1-0-3)  = Eq.refl
decode-codeM (Sb4-1-23-0)  = Eq.refl
decode-codeM (Sb4-1-3-0)   = Eq.refl
decode-codeM (Sb⁻4-1-0-2)  = Eq.refl
decode-codeM (Sb4-1-32-0)  = Eq.refl
decode-codeM (Sb4-2-0-3)   = Eq.refl
decode-codeM (Sb4-2-1-3)   = Eq.refl
decode-codeM (Sb⁻4-2-1-3)  = Eq.refl
decode-codeM (Sb4-2-03-1)  = Eq.refl
decode-codeM (Sb⁻4-2-0-3)  = Eq.refl
decode-codeM (Sb4-2-13-0)  = Eq.refl
decode-codeM (Sb4-2-3-0)   = Eq.refl
decode-codeM (Sb4-3-1-0)   = Eq.refl
decode-codeM (Sb4-3-2-0)   = Eq.refl
decode-codeM (Sb⁻0-1-23-4) = Eq.refl
decode-codeM (Sb⁻0-1-3-4)  = Eq.refl
decode-codeM (Sb⁻0-1-32-4) = Eq.refl
decode-codeM (Sb⁻0-1-34-2) = Eq.refl
decode-codeM (Sb⁻0-1-42-3) = Eq.refl
decode-codeM (Sb⁻0-1-43-2) = Eq.refl
decode-codeM (Sb⁻0-2-34-1) = Eq.refl
decode-codeM (Sb⁻0-2-43-1) = Eq.refl
decode-codeM (Sb⁻0-3-1-2)  = Eq.refl
decode-codeM (Sb⁻0-3-2-1)  = Eq.refl
decode-codeM (Sb⁻0-4-1-2)  = Eq.refl
decode-codeM (Sb⁻0-4-1-3)  = Eq.refl
decode-codeM (Sb⁻0-4-2-1)  = Eq.refl
decode-codeM (Sb⁻1-0-23-4) = Eq.refl
decode-codeM (Sb⁻1-0-24-3) = Eq.refl
decode-codeM (Sb⁻1-0-32-4) = Eq.refl
decode-codeM (Sb⁻1-0-34-2) = Eq.refl
decode-codeM (Sb⁻1-0-42-3) = Eq.refl
decode-codeM (Sb⁻1-0-43-2) = Eq.refl
decode-codeM (Sb⁻1-2-34-0) = Eq.refl
decode-codeM (Sb⁻1-2-4-0)  = Eq.refl
decode-codeM (Sb⁻1-2-40-3) = Eq.refl
decode-codeM (Sb⁻1-3-4-0)  = Eq.refl
decode-codeM (Sb⁻1-3-4-2)  = Eq.refl
decode-codeM (Sb⁻1-3-40-2) = Eq.refl
decode-codeM (Sb⁻1-4-20-3) = Eq.refl
decode-codeM (Sb⁻1-4-30-2) = Eq.refl
decode-codeM (Sb⁻2-0-13-4) = Eq.refl
decode-codeM (Sb⁻2-0-14-3) = Eq.refl
decode-codeM (Sb⁻2-0-31-4) = Eq.refl
decode-codeM (Sb⁻2-0-34-1) = Eq.refl
decode-codeM (Sb⁻2-0-41-3) = Eq.refl
decode-codeM (Sb⁻2-0-43-1) = Eq.refl
decode-codeM (Sb⁻2-1-34-0) = Eq.refl
decode-codeM (Sb⁻2-1-4-0)  = Eq.refl
decode-codeM (Sb⁻2-1-40-3) = Eq.refl
decode-codeM (Sb⁻2-3-4-0)  = Eq.refl
decode-codeM (Sb⁻2-3-4-1)  = Eq.refl
decode-codeM (Sb⁻2-4-01-3) = Eq.refl
decode-codeM (Sb⁻2-4-10-3) = Eq.refl
decode-codeM (Sb⁻3-0-41-2) = Eq.refl
decode-codeM (Sb⁻3-0-42-1) = Eq.refl
decode-codeM (Sb⁻3-1-0-4)  = Eq.refl
decode-codeM (Sb⁻3-1-4-0)  = Eq.refl
decode-codeM (Sb⁻4-0-23-1) = Eq.refl
decode-codeM (Sb⁻4-0-31-2) = Eq.refl
decode-codeM (Sb⁻4-0-32-1) = Eq.refl
decode-codeM (Sb⁻4-1-2-0)  = Eq.refl
decode-codeM (Sb⁻4-1-23-0) = Eq.refl
decode-codeM (Sb⁻4-1-3-0)  = Eq.refl
decode-codeM (Sb⁻4-1-32-0) = Eq.refl

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

run : List Step → List Mac → Maybe (List Mac)
run []                xs = just xs
run (rw k e ∷ ss)     xs =
  if eqLM (take (length (lhs e)) (drop k xs)) (lhs e)
  then run ss (next k (length (lhs e)) (rhs e) xs) else nothing
run (rw⁻ k e ∷ ss)    xs =
  if eqLM (take (length (rhs e)) (drop k xs)) (rhs e)
  then run ss (next k (length (rhs e)) (lhs e) xs) else nothing
run (re k n ys ∷ ss)  xs =
  if eqLG (flat (take n (drop k xs))) (flat ys)
  then run ss (next k n ys xs) else nothing

check : List Step → List Mac → List Mac → Bool
check ss l r with run ss l
... | just xs = eqLM xs r
... | nothing = false

private
  ≡⇒≈ : ∀ {xs ys} → xs ≡ ys → ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
  ≡⇒≈ Eq.refl = refl

run-sound : (ss : List Step) (xs ys : List Mac) → run ss xs ≡ just ys → ⟪ xs ⟫ʷ ≈ ⟪ ys ⟫ʷ
run-sound []               xs ys Eq.refl = refl
run-sound (rw k e ∷ ss)    xs ys h with eqLM (take (length (lhs e)) (drop k xs)) (lhs e) in c
run-sound (rw k e ∷ ss)    xs ys h  | true  =
  trans (step k (length (lhs e)) xs (rhs e) (trans (≡⇒≈ (eqLM-sound (take (length (lhs e)) (drop k xs)) (lhs e) c)) (prf e)))
        (run-sound ss _ ys h)
run-sound (rw k e ∷ ss)    xs ys () | false
run-sound (rw⁻ k e ∷ ss)   xs ys h with eqLM (take (length (rhs e)) (drop k xs)) (rhs e) in c
run-sound (rw⁻ k e ∷ ss)   xs ys h  | true  =
  trans (step k (length (rhs e)) xs (lhs e) (trans (≡⇒≈ (eqLM-sound (take (length (rhs e)) (drop k xs)) (rhs e) c)) (sym (prf e))))
        (run-sound ss _ ys h)
run-sound (rw⁻ k e ∷ ss)   xs ys () | false
run-sound (re k n zs ∷ ss) xs ys h with eqLG (flat (take n (drop k xs))) (flat zs) in c
run-sound (re k n zs ∷ ss) xs ys h  | true  =
  trans (step k n xs zs (by-assoc {⟪ take n (drop k xs) ⟫ʷ} {⟪ zs ⟫ʷ} (eqLG-sound (flat (take n (drop k xs))) (flat zs) c))) (run-sound ss _ ys h)
run-sound (re k n zs ∷ ss) xs ys () | false

check-sound : (ss : List Step) (l r : List Mac) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
check-sound ss l r h with run ss l in e
check-sound ss l r h  | just xs = trans (run-sound ss l xs e) (≡⇒≈ (eqLM-sound xs r h))
check-sound ss l r () | nothing

-- The equation of a derivation, checked by running it.
derive : (l r : List Mac) (ss : List Step) → check ss l r ≡ true → ⟪ l ⟫ʷ ≈ ⟪ r ⟫ʷ
derive l r ss h = check-sound ss l r h
