{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The lemmas of Five/D that F5 uses, instantiated
--
-- Each derivation module takes the lemmas of the others that it uses
-- as a list (DSig); here every lemma that one uses, or that the
-- consumer does, is the lemma of its module applied to its list, in
-- dependency order.  Written by `scratchpad/four/di.py`.
------------------------------------------------------------------------

module Examples.Groups.Clifford+CS.Five.DAll.F5 where

open import Examples.Groups.Clifford+CS.Five.DSig
open import Examples.Groups.Clifford+CS.Five.WinSig using (lit)
import Examples.Groups.Clifford+CS.Five.D.R001 as R001
import Examples.Groups.Clifford+CS.Five.D.R002 as R002
import Examples.Groups.Clifford+CS.Five.D.R003 as R003
import Examples.Groups.Clifford+CS.Five.D.R005 as R005
import Examples.Groups.Clifford+CS.Five.D.R006 as R006
import Examples.Groups.Clifford+CS.Five.D.R007 as R007
import Examples.Groups.Clifford+CS.Five.D.R008 as R008
import Examples.Groups.Clifford+CS.Five.D.R009 as R009
import Examples.Groups.Clifford+CS.Five.D.D001 as D001
import Examples.Groups.Clifford+CS.Five.D.D002 as D002
import Examples.Groups.Clifford+CS.Five.D.D004 as D004
import Examples.Groups.Clifford+CS.Five.D.D006 as D006
import Examples.Groups.Clifford+CS.Five.D.R004 as R004
import Examples.Groups.Clifford+CS.Five.D.D003 as D003
import Examples.Groups.Clifford+CS.Five.D.D005 as D005
import Examples.Groups.Clifford+CS.Five.D.D007 as D007
import Examples.Groups.Clifford+CS.Five.D.D009 as D009
import Examples.Groups.Clifford+CS.Five.D.D010 as D010
import Examples.Groups.Clifford+CS.Five.D.D011 as D011
import Examples.Groups.Clifford+CS.Five.D.D008 as D008
import Examples.Groups.Clifford+CS.Five.D.D012 as D012
import Examples.Groups.Clifford+CS.Five.D.D014 as D014
import Examples.Groups.Clifford+CS.Five.D.D013 as D013
import Examples.Groups.Clifford+CS.Five.D.D015 as D015
import Examples.Groups.Clifford+CS.Five.D.D016 as D016
import Examples.Groups.Clifford+CS.Five.D.D018 as D018
import Examples.Groups.Clifford+CS.Five.D.D019 as D019
import Examples.Groups.Clifford+CS.Five.D.D020 as D020
import Examples.Groups.Clifford+CS.Five.D.D025 as D025

lem-comm-push-CS04-sw1-R : _
lem-comm-push-CS04-sw1-R = R001.lem-comm-push-CS04-sw1-R
lem-comm-push-CS04-sw2-R : _
lem-comm-push-CS04-sw2-R = R001.lem-comm-push-CS04-sw2-R
lem-comm-push-CS04-sw1-L : _
lem-comm-push-CS04-sw1-L = R001.lem-comm-push-CS04-sw1-L
lem-comm-push-CS04-sw0-L : _
lem-comm-push-CS04-sw0-L = R001.lem-comm-push-CS04-sw0-L
lem-comm-CX12-CCZ034 : _
lem-comm-CX12-CCZ034 = R001.lem-comm-CX12-CCZ034
lem-comm-CSd12-TOFF034 : _
lem-comm-CSd12-TOFF034 = R001.lem-comm-CSd12-TOFF034
lem-comm-CZ12-CCZ034 : _
lem-comm-CZ12-CCZ034 = R001.lem-comm-CZ12-CCZ034
lem-comm-CZ12-TOFF034 : _
lem-comm-CZ12-TOFF034 = R001.lem-comm-CZ12-TOFF034
lem-comm-push-CSd04-sw0-L : _
lem-comm-push-CSd04-sw0-L = R001.lem-comm-push-CSd04-sw0-L
lem-comm-TOFF204-CSd13 : _
lem-comm-TOFF204-CSd13 = R001.lem-comm-TOFF204-CSd13
lem-comm-push-CSd04-sw1-L : _
lem-comm-push-CSd04-sw1-L = R001.lem-comm-push-CSd04-sw1-L
lem-comm-push-CX04-sw0-L : _
lem-comm-push-CX04-sw0-L = R001.lem-comm-push-CX04-sw0-L
lem-comm-CX04-CCZ123 : _
lem-comm-CX04-CCZ123 = R001.lem-comm-CX04-CCZ123
lem-comm-CSd04-TOFF213 : _
lem-comm-CSd04-TOFF213 = R001.lem-comm-CSd04-TOFF213
lem-comm-CSd13-CCZ024 : _
lem-comm-CSd13-CCZ024 = R001.lem-comm-CSd13-CCZ024
lem-comm-CS13-CCZ024 : _
lem-comm-CS13-CCZ024 = R001.lem-comm-CS13-CCZ024
lem-comm-CX13-CCZ024 : _
lem-comm-CX13-CCZ024 = R001.lem-comm-CX13-CCZ024
lem-comm-push-CS04-sw2-L : _
lem-comm-push-CS04-sw2-L = R001.lem-comm-push-CS04-sw2-L
lem-comm-push-CX04-sw1-L : _
lem-comm-push-CX04-sw1-L = R001.lem-comm-push-CX04-sw1-L
lem-comm-CX04-TOFF213 : _
lem-comm-CX04-TOFF213 = R001.lem-comm-CX04-TOFF213
lem-comm-push-CZ04-sw0-L : _
lem-comm-push-CZ04-sw0-L = R001.lem-comm-push-CZ04-sw0-L
lem-comm-CZ04-CCZ123 : _
lem-comm-CZ04-CCZ123 = R001.lem-comm-CZ04-CCZ123
lem-comm-CZ04-TOFF213 : _
lem-comm-CZ04-TOFF213 = R001.lem-comm-CZ04-TOFF213
lem-comm-TOFF014-CSd23 : _
lem-comm-TOFF014-CSd23 = R001.lem-comm-TOFF014-CSd23
lem-comm-CX14-CCZ023 : _
lem-comm-CX14-CCZ023 = R001.lem-comm-CX14-CCZ023
lem-comm-CSd14-TOFF023 : _
lem-comm-CSd14-TOFF023 = R001.lem-comm-CSd14-TOFF023
lem-comm-CSd23-CCZ014 : _
lem-comm-CSd23-CCZ014 = R001.lem-comm-CSd23-CCZ014
lem-comm-CS23-CCZ014 : _
lem-comm-CS23-CCZ014 = R001.lem-comm-CS23-CCZ014
lem-comm-CX23-CCZ014 : _
lem-comm-CX23-CCZ014 = R001.lem-comm-CX23-CCZ014
lem-comm-CX14-TOFF023 : _
lem-comm-CX14-TOFF023 = R001.lem-comm-CX14-TOFF023
lem-comm-CZ14-CCZ023 : _
lem-comm-CZ14-CCZ023 = R001.lem-comm-CZ14-CCZ023
lem-comm-CZ14-TOFF023 : _
lem-comm-CZ14-TOFF023 = R001.lem-comm-CZ14-TOFF023
lem-comm-TOFF024-CSd13 : _
lem-comm-TOFF024-CSd13 = R001.lem-comm-TOFF024-CSd13
lem-comm-CX24-CCZ013 : _
lem-comm-CX24-CCZ013 = R001.lem-comm-CX24-CCZ013
lem-comm-CSd24-TOFF013 : _
lem-comm-CSd24-TOFF013 = R001.lem-comm-CSd24-TOFF013
lem-comm-CX24-TOFF013 : _
lem-comm-CX24-TOFF013 = R001.lem-comm-CX24-TOFF013
lem-comm-CZ24-CCZ013 : _
lem-comm-CZ24-CCZ013 = R001.lem-comm-CZ24-CCZ013
lem-comm-CZ24-TOFF013 : _
lem-comm-CZ24-TOFF013 = R001.lem-comm-CZ24-TOFF013
lem-comm-SWAP23-BOX⟨0·14⟩ : _
lem-comm-SWAP23-BOX⟨0·14⟩ = R001.lem-comm-SWAP23-BOX⟨0·14⟩
lem-comm-push-CSd04-sw2-L : _
lem-comm-push-CSd04-sw2-L = R001.lem-comm-push-CSd04-sw2-L
lem-comm-CX21-CCZ034 : _
lem-comm-CX21-CCZ034 = R001.lem-comm-CX21-CCZ034
lem-comm-SWAP13-BOX⟨0·24⟩ : _
lem-comm-SWAP13-BOX⟨0·24⟩ = R001.lem-comm-SWAP13-BOX⟨0·24⟩
lem-comm-CZ13-CCZ024 : _
lem-comm-CZ13-CCZ024 = R001.lem-comm-CZ13-CCZ024
lem-comm-TOFF013-CSd24 : _
lem-comm-TOFF013-CSd24 = R001.lem-comm-TOFF013-CSd24
lem-comm-CSd13-TOFF024 : _
lem-comm-CSd13-TOFF024 = R001.lem-comm-CSd13-TOFF024
lem-comm-CS12-TOFF034 : _
lem-comm-CS12-TOFF034 = R001.lem-comm-CS12-TOFF034
lem-comm-SWAP14-BOX⟨0·32⟩ : _
lem-comm-SWAP14-BOX⟨0·32⟩ = R001.lem-comm-SWAP14-BOX⟨0·32⟩
lem-comm-CZ23-CCZ014 : _
lem-comm-CZ23-CCZ014 = R001.lem-comm-CZ23-CCZ014
lem-comm-CSd23-TOFF014 : _
lem-comm-CSd23-TOFF014 = R001.lem-comm-CSd23-TOFF014
lem-comm-SWAP24-BOX⟨0·31⟩ : _
lem-comm-SWAP24-BOX⟨0·31⟩ = R001.lem-comm-SWAP24-BOX⟨0·31⟩
lem-comm-CX31-CCZ024 : _
lem-comm-CX31-CCZ024 = R001.lem-comm-CX31-CCZ024
lem-comm-CS13-TOFF024 : _
lem-comm-CS13-TOFF024 = R001.lem-comm-CS13-TOFF024
lem-comm-SWAP14-BOX⟨0·23⟩ : _
lem-comm-SWAP14-BOX⟨0·23⟩ = R001.lem-comm-SWAP14-BOX⟨0·23⟩
lem-comm-SWAP13-BOX⟨0·42⟩ : _
lem-comm-SWAP13-BOX⟨0·42⟩ = R001.lem-comm-SWAP13-BOX⟨0·42⟩
lem-comm-TOFF034-CSd12 : _
lem-comm-TOFF034-CSd12 = R001.lem-comm-TOFF034-CSd12
lem-comm-CX42-CCZ013 : _
lem-comm-CX42-CCZ013 = R001.lem-comm-CX42-CCZ013
lem-comm-CX32-CCZ014 : _
lem-comm-CX32-CCZ014 = R001.lem-comm-CX32-CCZ014
lem-comm-CSd12-CCZ034 : _
lem-comm-CSd12-CCZ034 = R001.lem-comm-CSd12-CCZ034
lem-comm-CS12-CCZ034 : _
lem-comm-CS12-CCZ034 = R001.lem-comm-CS12-CCZ034
lem-comm-CX12-TOFF034 : _
lem-comm-CX12-TOFF034 = R001.lem-comm-CX12-TOFF034
lem-comm-push-CZ04-sw2-L : _
lem-comm-push-CZ04-sw2-L = R001.lem-comm-push-CZ04-sw2-L
lem-comm-push-CZ04-sw1-L : _
lem-comm-push-CZ04-sw1-L = R001.lem-comm-push-CZ04-sw1-L
lem-comm-push-CX40-sw2-L : _
lem-comm-push-CX40-sw2-L = R001.lem-comm-push-CX40-sw2-L
lem-comm-push-CX40-sw1-L : _
lem-comm-push-CX40-sw1-L = R001.lem-comm-push-CX40-sw1-L
lem-comm-push-CX40-sw0-L : _
lem-comm-push-CX40-sw0-L = R001.lem-comm-push-CX40-sw0-L
lem-comm-push-CK40-sw0-L : _
lem-comm-push-CK40-sw0-L = R001.lem-comm-push-CK40-sw0-L
lem-comm-push-CKd40-sw0-L : _
lem-comm-push-CKd40-sw0-L = R001.lem-comm-push-CKd40-sw0-L
lem-comm-CX02-CCZ134 : _
lem-comm-CX02-CCZ134 = R001.lem-comm-CX02-CCZ134
lem-comm-CSd02-TOFF134 : _
lem-comm-CSd02-TOFF134 = R001.lem-comm-CSd02-TOFF134
lem-comm-CS14-TOFF023 : _
lem-comm-CS14-TOFF023 = R001.lem-comm-CS14-TOFF023
lem-comm-CS24-TOFF013 : _
lem-comm-CS24-TOFF013 = R001.lem-comm-CS24-TOFF013
lem-comm-TOFF301-CSd24 : _
lem-comm-TOFF301-CSd24 = R001.lem-comm-TOFF301-CSd24
lem-comm-CSd24-CCZ013 : _
lem-comm-CSd24-CCZ013 = R001.lem-comm-CSd24-CCZ013
lem-comm-CS24-CCZ013 : _
lem-comm-CS24-CCZ013 = R001.lem-comm-CS24-CCZ013
lem-comm-TOFF401-CSd23 : _
lem-comm-TOFF401-CSd23 = R001.lem-comm-TOFF401-CSd23
lem-comm-CS03-TOFF412 : _
lem-comm-CS03-TOFF412 = R001.lem-comm-CS03-TOFF412
lem-comm-TOFF412-CSd03 : _
lem-comm-TOFF412-CSd03 = R001.lem-comm-TOFF412-CSd03
lem-comm-CSd12-TOFF403 : _
lem-comm-CSd12-TOFF403 = R001.lem-comm-CSd12-TOFF403
lem-comm-CSd03-CCZ124 : _
lem-comm-CSd03-CCZ124 = R001.lem-comm-CSd03-CCZ124
lem-comm-CS03-CCZ124 : _
lem-comm-CS03-CCZ124 = R001.lem-comm-CS03-CCZ124
lem-comm-CZ03-TOFF412 : _
lem-comm-CZ03-TOFF412 = R001.lem-comm-CZ03-TOFF412
lem-comm-CSd03-TOFF412 : _
lem-comm-CSd03-TOFF412 = R001.lem-comm-CSd03-TOFF412
lem-comm-SWAP02-BOX⟨4·13⟩ : _
lem-comm-SWAP02-BOX⟨4·13⟩ = R001.lem-comm-SWAP02-BOX⟨4·13⟩
lem-comm-CZ04-TOFF312 : _
lem-comm-CZ04-TOFF312 = R001.lem-comm-CZ04-TOFF312
lem-comm-TOFF312-CSd04 : _
lem-comm-TOFF312-CSd04 = R001.lem-comm-TOFF312-CSd04
lem-comm-CSd12-TOFF304 : _
lem-comm-CSd12-TOFF304 = R002.lem-comm-CSd12-TOFF304
lem-comm-TOFF304-CSd12 : _
lem-comm-TOFF304-CSd12 = R002.lem-comm-TOFF304-CSd12
lem-comm-CX40-CCZ123 : _
lem-comm-CX40-CCZ123 = R002.lem-comm-CX40-CCZ123
lem-comm-CSd04-TOFF312 : _
lem-comm-CSd04-TOFF312 = R002.lem-comm-CSd04-TOFF312
lem-comm-CX40-TOFF312 : _
lem-comm-CX40-TOFF312 = R002.lem-comm-CX40-TOFF312
lem-comm-CZ12-TOFF304 : _
lem-comm-CZ12-TOFF304 = R002.lem-comm-CZ12-TOFF304
lem-comm-CSd23-TOFF401 : _
lem-comm-CSd23-TOFF401 = R002.lem-comm-CSd23-TOFF401
lem-comm-CS23-TOFF401 : _
lem-comm-CS23-TOFF401 = R002.lem-comm-CS23-TOFF401
lem-comm-CSd24-TOFF301 : _
lem-comm-CSd24-TOFF301 = R002.lem-comm-CSd24-TOFF301
lem-comm-CS24-TOFF301 : _
lem-comm-CS24-TOFF301 = R002.lem-comm-CS24-TOFF301
lem-comm-SWAP02-BOX⟨3·14⟩ : _
lem-comm-SWAP02-BOX⟨3·14⟩ = R002.lem-comm-SWAP02-BOX⟨3·14⟩
lem-comm-CZ12-TOFF403 : _
lem-comm-CZ12-TOFF403 = R002.lem-comm-CZ12-TOFF403
lem-comm-CS04-TOFF312 : _
lem-comm-CS04-TOFF312 = R002.lem-comm-CS04-TOFF312
lem-comm-TOFF312-CS04 : _
lem-comm-TOFF312-CS04 = R002.lem-comm-TOFF312-CS04
lem-comm-CS04-TOFF213 : _
lem-comm-CS04-TOFF213 = R002.lem-comm-CS04-TOFF213
lem-comm-CSd14-CCZ023 : _
lem-comm-CSd14-CCZ023 = R002.lem-comm-CSd14-CCZ023
lem-comm-CS14-CCZ023 : _
lem-comm-CS14-CCZ023 = R002.lem-comm-CS14-CCZ023
lem-comm-push-CK40-sw1-L : _
lem-comm-push-CK40-sw1-L = R002.lem-comm-push-CK40-sw1-L
lem-comm-CSd04-CCZ123 : _
lem-comm-CSd04-CCZ123 = R002.lem-comm-CSd04-CCZ123
lem-comm-CS04-CCZ123 : _
lem-comm-CS04-CCZ123 = R002.lem-comm-CS04-CCZ123
lem-comm-CK40-TOFF213 : _
lem-comm-CK40-TOFF213 = R002.lem-comm-CK40-TOFF213
lem-comm-push-CK40-sw2-L : _
lem-comm-push-CK40-sw2-L = R002.lem-comm-push-CK40-sw2-L
lem-comm-CSd13-TOFF204 : _
lem-comm-CSd13-TOFF204 = R002.lem-comm-CSd13-TOFF204
lem-comm-CS13-TOFF204 : _
lem-comm-CS13-TOFF204 = R002.lem-comm-CS13-TOFF204
lem-comm-CX41-CCZ023 : _
lem-comm-CX41-CCZ023 = R002.lem-comm-CX41-CCZ023
lem-comm-CZ03-TOFF214 : _
lem-comm-CZ03-TOFF214 = R002.lem-comm-CZ03-TOFF214
lem-comm-TOFF214-CSd03 : _
lem-comm-TOFF214-CSd03 = R002.lem-comm-TOFF214-CSd03
lem-comm-CSd14-TOFF203 : _
lem-comm-CSd14-TOFF203 = R002.lem-comm-CSd14-TOFF203
lem-comm-CZ03-CCZ124 : _
lem-comm-CZ03-CCZ124 = R002.lem-comm-CZ03-CCZ124
lem-comm-CX03-CCZ124 : _
lem-comm-CX03-CCZ124 = R002.lem-comm-CX03-CCZ124
lem-comm-CSd03-TOFF214 : _
lem-comm-CSd03-TOFF214 = R002.lem-comm-CSd03-TOFF214
lem-comm-CK41-CCZ023 : _
lem-comm-CK41-CCZ023 = R002.lem-comm-CK41-CCZ023
lem-comm-CK41-TOFF023 : _
lem-comm-CK41-TOFF023 = R002.lem-comm-CK41-TOFF023
lem-comm-CS23-TOFF014 : _
lem-comm-CS23-TOFF014 = R002.lem-comm-CS23-TOFF014
lem-comm-CZ13-TOFF024 : _
lem-comm-CZ13-TOFF024 = R002.lem-comm-CZ13-TOFF024
lem-comm-CK42-TOFF013 : _
lem-comm-CK42-TOFF013 = R002.lem-comm-CK42-TOFF013
lem-comm-SWAP14-BOX⟨2·03⟩ : _
lem-comm-SWAP14-BOX⟨2·03⟩ = R002.lem-comm-SWAP14-BOX⟨2·03⟩
lem-comm-SWAP24-BOX⟨0·13⟩ : _
lem-comm-SWAP24-BOX⟨0·13⟩ = R002.lem-comm-SWAP24-BOX⟨0·13⟩
lem-comm-SWAP23-BOX⟨0·41⟩ : _
lem-comm-SWAP23-BOX⟨0·41⟩ = R002.lem-comm-SWAP23-BOX⟨0·41⟩
lem-comm-TOFF213-CSd04 : _
lem-comm-TOFF213-CSd04 = R002.lem-comm-TOFF213-CSd04
lem-comm-TOFF213-CK40 : _
lem-comm-TOFF213-CK40 = R002.lem-comm-TOFF213-CK40
lem-comm-TOFF013-CK42 : _
lem-comm-TOFF013-CK42 = R002.lem-comm-TOFF013-CK42
lem-comm-CCZ024-CX13 : _
lem-comm-CCZ024-CX13 = R002.lem-comm-CCZ024-CX13
lem-comm-TOFF213-CX04 : _
lem-comm-TOFF213-CX04 = R002.lem-comm-TOFF213-CX04
lem-comm-CZ02-TOFF314 : _
lem-comm-CZ02-TOFF314 = R002.lem-comm-CZ02-TOFF314
lem-comm-CSd02-TOFF314 : _
lem-comm-CSd02-TOFF314 = R002.lem-comm-CSd02-TOFF314
lem-comm-CS02-TOFF314 : _
lem-comm-CS02-TOFF314 = R002.lem-comm-CS02-TOFF314
lem-comm-CX04-TOFF312 : _
lem-comm-CX04-TOFF312 = R002.lem-comm-CX04-TOFF312
lem-comm-CX30-CCZ124 : _
lem-comm-CX30-CCZ124 = R002.lem-comm-CX30-CCZ124
lem-comm-CX30-TOFF214 : _
lem-comm-CX30-TOFF214 = R002.lem-comm-CX30-TOFF214
lem-comm-CZ14-TOFF203 : _
lem-comm-CZ14-TOFF203 = R002.lem-comm-CZ14-TOFF203
lem-comm-CS12-TOFF304 : _
lem-comm-CS12-TOFF304 = R002.lem-comm-CS12-TOFF304
lem-comm-TOFF314-CSd02 : _
lem-comm-TOFF314-CSd02 = R002.lem-comm-TOFF314-CSd02
lem-comm-CSd14-TOFF302 : _
lem-comm-CSd14-TOFF302 = R002.lem-comm-CSd14-TOFF302
lem-comm-CSd02-CCZ134 : _
lem-comm-CSd02-CCZ134 = R002.lem-comm-CSd02-CCZ134
lem-comm-CS02-CCZ134 : _
lem-comm-CS02-CCZ134 = R002.lem-comm-CS02-CCZ134
lem-comm-CZ14-TOFF302 : _
lem-comm-CZ14-TOFF302 = R002.lem-comm-CZ14-TOFF302
lem-comm-CS03-TOFF214 : _
lem-comm-CS03-TOFF214 = R002.lem-comm-CS03-TOFF214
lem-comm-TOFF214-CS03 : _
lem-comm-TOFF214-CS03 = R002.lem-comm-TOFF214-CS03
lem-comm-CZ23-TOFF014 : _
lem-comm-CZ23-TOFF014 = R002.lem-comm-CZ23-TOFF014
lem-comm-CZ24-TOFF301 : _
lem-comm-CZ24-TOFF301 = R002.lem-comm-CZ24-TOFF301
lem-comm-SWAP14-BOX⟨3·20⟩ : _
lem-comm-SWAP14-BOX⟨3·20⟩ = R002.lem-comm-SWAP14-BOX⟨3·20⟩
lem-comm-CZ13-TOFF204 : _
lem-comm-CZ13-TOFF204 = R002.lem-comm-CZ13-TOFF204
lem-comm-push-SWAP04-sw2-L : _
lem-comm-push-SWAP04-sw2-L = R002.lem-comm-push-SWAP04-sw2-L
lem-comm-SWAP14-BOX⟨2·30⟩ : _
lem-comm-SWAP14-BOX⟨2·30⟩ = R002.lem-comm-SWAP14-BOX⟨2·30⟩
lem-comm-CX21-TOFF034 : _
lem-comm-CX21-TOFF034 = R002.lem-comm-CX21-TOFF034
lem-comm-CCZ024-CX31 : _
lem-comm-CCZ024-CX31 = R002.lem-comm-CCZ024-CX31
lem-comm-CCZ014-CX23 : _
lem-comm-CCZ014-CX23 = R002.lem-comm-CCZ014-CX23
lem-comm-TOFF013-CX24 : _
lem-comm-TOFF013-CX24 = R002.lem-comm-TOFF013-CX24
lem-comm-SWAP12-BOX⟨3·04⟩ : _
lem-comm-SWAP12-BOX⟨3·04⟩ = R002.lem-comm-SWAP12-BOX⟨3·04⟩
lem-comm-CS14-TOFF203 : _
lem-comm-CS14-TOFF203 = R002.lem-comm-CS14-TOFF203
lem-comm-SWAP12-BOX⟨3·40⟩ : _
lem-comm-SWAP12-BOX⟨3·40⟩ = R002.lem-comm-SWAP12-BOX⟨3·40⟩
lem-comm-CZ02-CCZ134 : _
lem-comm-CZ02-CCZ134 = R003.lem-comm-CZ02-CCZ134
lem-comm-CS14-TOFF302 : _
lem-comm-CS14-TOFF302 = R003.lem-comm-CS14-TOFF302
lem-comm-SWAP14-BOX⟨3·02⟩ : _
lem-comm-SWAP14-BOX⟨3·02⟩ = R003.lem-comm-SWAP14-BOX⟨3·02⟩
lem-comm-CX20-CCZ134 : _
lem-comm-CX20-CCZ134 = R003.lem-comm-CX20-CCZ134
lem-comm-push-SWAP04-sw0-L : _
lem-comm-push-SWAP04-sw0-L = R003.lem-comm-push-SWAP04-sw0-L
lem-comm-push-CX04-sw2-L : _
lem-comm-push-CX04-sw2-L = R003.lem-comm-push-CX04-sw2-L
lem-comm-SWAP04-BOX⟨3·21⟩ : _
lem-comm-SWAP04-BOX⟨3·21⟩ = R003.lem-comm-SWAP04-BOX⟨3·21⟩
lem-comm-SWAP02-BOX⟨3·41⟩ : _
lem-comm-SWAP02-BOX⟨3·41⟩ = R003.lem-comm-SWAP02-BOX⟨3·41⟩
lem-comm-CK40-TOFF312 : _
lem-comm-CK40-TOFF312 = R003.lem-comm-CK40-TOFF312
lem-comm-SWAP13-BOX⟨2·04⟩ : _
lem-comm-SWAP13-BOX⟨2·04⟩ = R003.lem-comm-SWAP13-BOX⟨2·04⟩
lem-comm-push-BOX⟨2·03⟩-sw1-L : _
lem-comm-push-BOX⟨2·03⟩-sw1-L = R003.lem-comm-push-BOX⟨2·03⟩-sw1-L
lem-comm-push-BOX⟨1·03⟩-sw0-L : _
lem-comm-push-BOX⟨1·03⟩-sw0-L = R003.lem-comm-push-BOX⟨1·03⟩-sw0-L
lem-comm-push-CSd14-sw0-L : _
lem-comm-push-CSd14-sw0-L = R003.lem-comm-push-CSd14-sw0-L
lem-comm-push-CS14-sw0-L : _
lem-comm-push-CS14-sw0-L = R003.lem-comm-push-CS14-sw0-L
lem-comm-push-BOX⟨0·13⟩-sw2-L : _
lem-comm-push-BOX⟨0·13⟩-sw2-L = R003.lem-comm-push-BOX⟨0·13⟩-sw2-L
lem-comm-push-BOX⟨0·12⟩-sw1-L : _
lem-comm-push-BOX⟨0·12⟩-sw1-L = R003.lem-comm-push-BOX⟨0·12⟩-sw1-L
lem-comm-push-BOX⟨0·21⟩-sw1-R : _
lem-comm-push-BOX⟨0·21⟩-sw1-R = R003.lem-comm-push-BOX⟨0·21⟩-sw1-R
lem-comm-push-BOX⟨0·12⟩-sw2-R : _
lem-comm-push-BOX⟨0·12⟩-sw2-R = R003.lem-comm-push-BOX⟨0·12⟩-sw2-R
lem-comm-push-CS14-sw0-R : _
lem-comm-push-CS14-sw0-R = R003.lem-comm-push-CS14-sw0-R
lem-comm-push-CSd14-sw0-R : _
lem-comm-push-CSd14-sw0-R = R003.lem-comm-push-CSd14-sw0-R
lem-comm-push-CS04-sw0-R : _
lem-comm-push-CS04-sw0-R = R003.lem-comm-push-CS04-sw0-R
lem-comm-push-BOX⟨0·13⟩-sw0-R : _
lem-comm-push-BOX⟨0·13⟩-sw0-R = R003.lem-comm-push-BOX⟨0·13⟩-sw0-R
lem-comm-push-BOX⟨1·03⟩-sw1-R : _
lem-comm-push-BOX⟨1·03⟩-sw1-R = R003.lem-comm-push-BOX⟨1·03⟩-sw1-R
lem-comm-push-BOX⟨4·203⟩-sw1-L : _
lem-comm-push-BOX⟨4·203⟩-sw1-L = R003.lem-comm-push-BOX⟨4·203⟩-sw1-L
lem-comm-push-BOX⟨0·43⟩-sw2-L : _
lem-comm-push-BOX⟨0·43⟩-sw2-L = R003.lem-comm-push-BOX⟨0·43⟩-sw2-L
lem-comm-push-BOX⟨0·42⟩-sw1-L : _
lem-comm-push-BOX⟨0·42⟩-sw1-L = R003.lem-comm-push-BOX⟨0·42⟩-sw1-L
lem-comm-push-BOX⟨0·41⟩-sw3-L : _
lem-comm-push-BOX⟨0·41⟩-sw3-L = R003.lem-comm-push-BOX⟨0·41⟩-sw3-L
lem-comm-push-CX04-sw2-R : _
lem-comm-push-CX04-sw2-R = R003.lem-comm-push-CX04-sw2-R
lem-comm-push-CX04-sw1-R : _
lem-comm-push-CX04-sw1-R = R003.lem-comm-push-CX04-sw1-R
lem-comm-push-BOX⟨0·31⟩-sw2-L : _
lem-comm-push-BOX⟨0·31⟩-sw2-L = R003.lem-comm-push-BOX⟨0·31⟩-sw2-L
lem-comm-push-BOX⟨0·21⟩-sw2-R : _
lem-comm-push-BOX⟨0·21⟩-sw2-R = R003.lem-comm-push-BOX⟨0·21⟩-sw2-R
lem-comm-push-BOX⟨0·31⟩-sw3-R : _
lem-comm-push-BOX⟨0·31⟩-sw3-R = R003.lem-comm-push-BOX⟨0·31⟩-sw3-R
lem-comm-push-BOX⟨0·41⟩-sw1-R : _
lem-comm-push-BOX⟨0·41⟩-sw1-R = R003.lem-comm-push-BOX⟨0·41⟩-sw1-R
lem-comm-push-BOX⟨0·42⟩-sw2-R : _
lem-comm-push-BOX⟨0·42⟩-sw2-R = R003.lem-comm-push-BOX⟨0·42⟩-sw2-R
lem-comm-push-BOX⟨4·103⟩-sw1-R : _
lem-comm-push-BOX⟨4·103⟩-sw1-R = R003.lem-comm-push-BOX⟨4·103⟩-sw1-R
lem-comm-push-BOX⟨0·21⟩-sw0-R : _
lem-comm-push-BOX⟨0·21⟩-sw0-R = R003.lem-comm-push-BOX⟨0·21⟩-sw0-R
lem-comm-push-BOX⟨1·20⟩-sw1-R : _
lem-comm-push-BOX⟨1·20⟩-sw1-R = R003.lem-comm-push-BOX⟨1·20⟩-sw1-R
lem-comm-push-BOX⟨1·230⟩-sw2-R : _
lem-comm-push-BOX⟨1·230⟩-sw2-R = R003.lem-comm-push-BOX⟨1·230⟩-sw2-R
lem-comm-push-BOX⟨1·320⟩-sw3-R : _
lem-comm-push-BOX⟨1·320⟩-sw3-R = R003.lem-comm-push-BOX⟨1·320⟩-sw3-R
lem-comm-push-BOX⟨1·420⟩-sw2-R : _
lem-comm-push-BOX⟨1·420⟩-sw2-R = R003.lem-comm-push-BOX⟨1·420⟩-sw2-R
lem-comm-push-BOX⟨4·10⟩-sw1-R : _
lem-comm-push-BOX⟨4·10⟩-sw1-R = R003.lem-comm-push-BOX⟨4·10⟩-sw1-R
lem-comm-push-BOX⟨4·20⟩-sw0-R : _
lem-comm-push-BOX⟨4·20⟩-sw0-R = R003.lem-comm-push-BOX⟨4·20⟩-sw0-R
lem-comm-CSd13-TOFF402 : _
lem-comm-CSd13-TOFF402 = R003.lem-comm-CSd13-TOFF402
lem-comm-CS13-TOFF402 : _
lem-comm-CS13-TOFF402 = R003.lem-comm-CS13-TOFF402
lem-comm-SWAP03-BOX⟨4·21⟩ : _
lem-comm-SWAP03-BOX⟨4·21⟩ = R003.lem-comm-SWAP03-BOX⟨4·21⟩
lem-comm-TOFF402-CSd13 : _
lem-comm-TOFF402-CSd13 = R003.lem-comm-TOFF402-CSd13
lem-comm-CSd02-TOFF413 : _
lem-comm-CSd02-TOFF413 = R003.lem-comm-CSd02-TOFF413
lem-comm-push-BOX⟨2·03⟩-sw2-R : _
lem-comm-push-BOX⟨2·03⟩-sw2-R = R003.lem-comm-push-BOX⟨2·03⟩-sw2-R
lem-comm-push-BOX⟨0·312⟩-sw3-R : _
lem-comm-push-BOX⟨0·312⟩-sw3-R = R003.lem-comm-push-BOX⟨0·312⟩-sw3-R
lem-comm-push-BOX⟨4·02⟩-sw2-R : _
lem-comm-push-BOX⟨4·02⟩-sw2-R = R003.lem-comm-push-BOX⟨4·02⟩-sw2-R
lem-comm-push-BOX⟨4·03⟩-sw1-R : _
lem-comm-push-BOX⟨4·03⟩-sw1-R = R003.lem-comm-push-BOX⟨4·03⟩-sw1-R
lem-comm-push-BOX⟨4·03⟩-sw0-R : _
lem-comm-push-BOX⟨4·03⟩-sw0-R = R003.lem-comm-push-BOX⟨4·03⟩-sw0-R
lem-comm-SWAP12-BOX⟨4·03⟩ : _
lem-comm-SWAP12-BOX⟨4·03⟩ = R003.lem-comm-SWAP12-BOX⟨4·03⟩
lem-comm-CZ13-TOFF402 : _
lem-comm-CZ13-TOFF402 = R003.lem-comm-CZ13-TOFF402
lem-comm-TOFF413-CSd02 : _
lem-comm-TOFF413-CSd02 = R003.lem-comm-TOFF413-CSd02
lem-comm-CZ23-TOFF401 : _
lem-comm-CZ23-TOFF401 = R003.lem-comm-CZ23-TOFF401
sR005 : SR005
sR005 = lem-comm-push-CS04-sw0-L ∷ᵃ lem-comm-push-CS04-sw1-L ∷ᵃ lem-comm-push-CS04-sw1-R ∷ᵃ lem-comm-push-CS04-sw2-L ∷ᵃ lem-comm-push-CS04-sw2-R ∷ᵃ lem-comm-push-CSd04-sw0-L ∷ᵃ lem-comm-push-CSd04-sw1-L ∷ᵃ lem-comm-push-CSd04-sw2-L ∷ᵃ lem-comm-push-CX04-sw0-L ∷ᵃ lem-comm-push-CX04-sw1-L ∷ᵃ lem-comm-push-CZ04-sw0-L ∷ᵃ nil
lem-comm-push-CCZ034-sw1-L : _
lem-comm-push-CCZ034-sw1-L = R005.lem-comm-push-CCZ034-sw1-L sR005
lem-comm-push-CCZ034-sw0-L : _
lem-comm-push-CCZ034-sw0-L = R005.lem-comm-push-CCZ034-sw0-L sR005
lem-comm-push-TOFF034-sw0-L : _
lem-comm-push-TOFF034-sw0-L = R005.lem-comm-push-TOFF034-sw0-L sR005
lem-comm-push-TOFF034-sw1-L : _
lem-comm-push-TOFF034-sw1-L = R005.lem-comm-push-TOFF034-sw1-L sR005
lem-comm-push-CCZ024-sw0-L : _
lem-comm-push-CCZ024-sw0-L = R005.lem-comm-push-CCZ024-sw0-L sR005
lem-comm-push-TOFF204-sw0-L : _
lem-comm-push-TOFF204-sw0-L = R005.lem-comm-push-TOFF204-sw0-L sR005
lem-comm-push-CCZ014-sw2-L : _
lem-comm-push-CCZ014-sw2-L = R005.lem-comm-push-CCZ014-sw2-L sR005
lem-comm-push-TOFF024-sw0-L : _
lem-comm-push-TOFF024-sw0-L = R005.lem-comm-push-TOFF024-sw0-L sR005
lem-comm-push-TOFF401-sw2-L : _
lem-comm-push-TOFF401-sw2-L = R005.lem-comm-push-TOFF401-sw2-L sR005
lem-comm-push-TOFF402-sw0-L : _
lem-comm-push-TOFF402-sw0-L = R005.lem-comm-push-TOFF402-sw0-L sR005
lem-comm-push-TOFF304-sw1-L : _
lem-comm-push-TOFF304-sw1-L = R005.lem-comm-push-TOFF304-sw1-L sR005
lem-comm-push-TOFF304-sw0-L : _
lem-comm-push-TOFF304-sw0-L = R005.lem-comm-push-TOFF304-sw0-L sR005
lem-comm-push-TOFF023-sw3-L : _
lem-comm-push-TOFF023-sw3-L = R005.lem-comm-push-TOFF023-sw3-L sR005
lem-comm-push-TOFF024-sw3-L : _
lem-comm-push-TOFF024-sw3-L = R005.lem-comm-push-TOFF024-sw3-L sR005
sR006 : SR006
sR006 = lem-comm-push-CK40-sw0-L ∷ᵃ lem-comm-push-CKd40-sw0-L ∷ᵃ lem-comm-push-CS04-sw0-L ∷ᵃ lem-comm-push-CS04-sw1-L ∷ᵃ lem-comm-push-CS04-sw1-R ∷ᵃ lem-comm-push-CS04-sw2-L ∷ᵃ lem-comm-push-CS04-sw2-R ∷ᵃ lem-comm-push-CX04-sw0-L ∷ᵃ lem-comm-push-CX04-sw1-L ∷ᵃ lem-comm-push-CX40-sw0-L ∷ᵃ lem-comm-push-CX40-sw1-L ∷ᵃ lem-comm-push-CX40-sw2-L ∷ᵃ lem-comm-push-CZ04-sw0-L ∷ᵃ lem-comm-push-CZ04-sw1-L ∷ᵃ lem-comm-push-CZ04-sw2-L ∷ᵃ lem-comm-push-CK40-sw1-L ∷ᵃ lem-comm-push-CK40-sw2-L ∷ᵃ lem-comm-push-SWAP04-sw2-L ∷ᵃ lem-comm-push-BOX⟨0·12⟩-sw1-L ∷ᵃ lem-comm-push-BOX⟨0·12⟩-sw2-R ∷ᵃ lem-comm-push-BOX⟨0·13⟩-sw2-L ∷ᵃ lem-comm-push-BOX⟨0·21⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨1·03⟩-sw0-L ∷ᵃ lem-comm-push-BOX⟨2·03⟩-sw1-L ∷ᵃ lem-comm-push-CS14-sw0-L ∷ᵃ lem-comm-push-CSd14-sw0-L ∷ᵃ lem-comm-push-CX04-sw2-L ∷ᵃ lem-comm-push-SWAP04-sw0-L ∷ᵃ nil
lem-comm-push-TOFF403-sw1-L : _
lem-comm-push-TOFF403-sw1-L = R006.lem-comm-push-TOFF403-sw1-L sR006
lem-comm-push-TOFF403-sw0-L : _
lem-comm-push-TOFF403-sw0-L = R006.lem-comm-push-TOFF403-sw0-L sR006
lem-comm-push-TOFF014-sw2-L : _
lem-comm-push-TOFF014-sw2-L = R006.lem-comm-push-TOFF014-sw2-L sR006
lem-comm-push-TOFF104-sw2-L : _
lem-comm-push-TOFF104-sw2-L = R006.lem-comm-push-TOFF104-sw2-L sR006
lem-comm-push-TOFF203-sw3-L : _
lem-comm-push-TOFF203-sw3-L = R006.lem-comm-push-TOFF203-sw3-L sR006
lem-comm-push-TOFF204-sw3-L : _
lem-comm-push-TOFF204-sw3-L = R006.lem-comm-push-TOFF204-sw3-L sR006
lem-comm-push-CCZ023-sw3-L : _
lem-comm-push-CCZ023-sw3-L = R006.lem-comm-push-CCZ023-sw3-L sR006
lem-comm-push-CCZ024-sw3-L : _
lem-comm-push-CCZ024-sw3-L = R006.lem-comm-push-CCZ024-sw3-L sR006
lem-comm-SWAP03-BOX⟨2·14⟩ : _
lem-comm-SWAP03-BOX⟨2·14⟩ = R006.lem-comm-SWAP03-BOX⟨2·14⟩ sR006
lem-comm-push-TOFF302-sw3-L : _
lem-comm-push-TOFF302-sw3-L = R006.lem-comm-push-TOFF302-sw3-L sR006
lem-comm-push-TOFF402-sw3-L : _
lem-comm-push-TOFF402-sw3-L = R006.lem-comm-push-TOFF402-sw3-L sR006
lem-comm-SWAP03-BOX⟨2·41⟩ : _
lem-comm-SWAP03-BOX⟨2·41⟩ = R006.lem-comm-SWAP03-BOX⟨2·41⟩ sR006
lem-comm-push-BOX⟨0·213⟩-sw1-L : _
lem-comm-push-BOX⟨0·213⟩-sw1-L = R006.lem-comm-push-BOX⟨0·213⟩-sw1-L sR006
lem-comm-push-BOX⟨0·123⟩-sw0-L : _
lem-comm-push-BOX⟨0·123⟩-sw0-L = R006.lem-comm-push-BOX⟨0·123⟩-sw0-L sR006
lem-comm-push-CCZ014-sw0-L : _
lem-comm-push-CCZ014-sw0-L = R006.lem-comm-push-CCZ014-sw0-L sR006
lem-comm-push-TOFF104-sw0-L : _
lem-comm-push-TOFF104-sw0-L = R006.lem-comm-push-TOFF104-sw0-L sR006
lem-comm-push-BOX⟨1·023⟩-sw2-L : _
lem-comm-push-BOX⟨1·023⟩-sw2-L = R006.lem-comm-push-BOX⟨1·023⟩-sw2-L sR006
lem-comm-push-BOX⟨1·032⟩-sw1-L : _
lem-comm-push-BOX⟨1·032⟩-sw1-L = R006.lem-comm-push-BOX⟨1·032⟩-sw1-L sR006
lem-comm-push-BOX⟨2·031⟩-sw1-R : _
lem-comm-push-BOX⟨2·031⟩-sw1-R = R006.lem-comm-push-BOX⟨2·031⟩-sw1-R sR006
lem-comm-push-CCZ014-sw2-R : _
lem-comm-push-CCZ014-sw2-R = R006.lem-comm-push-CCZ014-sw2-R sR006
lem-comm-push-TOFF014-sw2-R : _
lem-comm-push-TOFF014-sw2-R = R006.lem-comm-push-TOFF014-sw2-R sR006
lem-comm-push-BOX⟨1·032⟩-sw2-R : _
lem-comm-push-BOX⟨1·032⟩-sw2-R = R006.lem-comm-push-BOX⟨1·032⟩-sw2-R sR006
sR007 : SR007
sR007 = lem-comm-push-CS04-sw0-L ∷ᵃ lem-comm-push-CS04-sw1-R ∷ᵃ lem-comm-push-CS04-sw2-R ∷ᵃ lem-comm-push-BOX⟨0·13⟩-sw0-R ∷ᵃ lem-comm-push-BOX⟨0·21⟩-sw2-R ∷ᵃ lem-comm-push-BOX⟨0·31⟩-sw2-L ∷ᵃ lem-comm-push-BOX⟨0·41⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨0·42⟩-sw1-L ∷ᵃ lem-comm-push-BOX⟨1·03⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨4·203⟩-sw1-L ∷ᵃ lem-comm-push-CS04-sw0-R ∷ᵃ lem-comm-push-CS14-sw0-L ∷ᵃ lem-comm-push-CS14-sw0-R ∷ᵃ lem-comm-push-CSd14-sw0-L ∷ᵃ lem-comm-push-CSd14-sw0-R ∷ᵃ lem-comm-push-CX04-sw1-R ∷ᵃ lem-comm-push-CX04-sw2-R ∷ᵃ nil
lem-comm-push-CCZ014-sw0-R : _
lem-comm-push-CCZ014-sw0-R = R007.lem-comm-push-CCZ014-sw0-R sR007
lem-comm-push-TOFF014-sw0-R : _
lem-comm-push-TOFF014-sw0-R = R007.lem-comm-push-TOFF014-sw0-R sR007
lem-comm-push-BOX⟨1·023⟩-sw0-R : _
lem-comm-push-BOX⟨1·023⟩-sw0-R = R007.lem-comm-push-BOX⟨1·023⟩-sw0-R sR007
lem-comm-push-BOX⟨0·123⟩-sw1-R : _
lem-comm-push-BOX⟨0·123⟩-sw1-R = R007.lem-comm-push-BOX⟨0·123⟩-sw1-R sR007
lem-comm-push-CCZ124-sw0-L : _
lem-comm-push-CCZ124-sw0-L = R007.lem-comm-push-CCZ124-sw0-L sR007
lem-comm-push-TOFF412-sw0-L : _
lem-comm-push-TOFF412-sw0-L = R007.lem-comm-push-TOFF412-sw0-L sR007
lem-comm-push-BOX⟨2·4103⟩-sw1-L : _
lem-comm-push-BOX⟨2·4103⟩-sw1-L = R007.lem-comm-push-BOX⟨2·4103⟩-sw1-L sR007
lem-comm-push-TOFF401-sw0-L : _
lem-comm-push-TOFF401-sw0-L = R007.lem-comm-push-TOFF401-sw0-L sR007
lem-comm-push-BOX⟨4·012⟩-sw1-L : _
lem-comm-push-BOX⟨4·012⟩-sw1-L = R007.lem-comm-push-BOX⟨4·012⟩-sw1-L sR007
lem-comm-push-BOX⟨3·021⟩-sw2-L : _
lem-comm-push-BOX⟨3·021⟩-sw2-L = R007.lem-comm-push-BOX⟨3·021⟩-sw2-L sR007
lem-comm-push-BOX⟨2·031⟩-sw2-R : _
lem-comm-push-BOX⟨2·031⟩-sw2-R = R007.lem-comm-push-BOX⟨2·031⟩-sw2-R sR007
lem-comm-push-CCZ034-sw3-R : _
lem-comm-push-CCZ034-sw3-R = R007.lem-comm-push-CCZ034-sw3-R sR007
lem-comm-push-CCZ023-sw3-R : _
lem-comm-push-CCZ023-sw3-R = R007.lem-comm-push-CCZ023-sw3-R sR007
lem-comm-push-TOFF302-sw3-R : _
lem-comm-push-TOFF302-sw3-R = R007.lem-comm-push-TOFF302-sw3-R sR007
lem-comm-push-CCZ034-sw1-R : _
lem-comm-push-CCZ034-sw1-R = R007.lem-comm-push-CCZ034-sw1-R sR007
lem-comm-push-TOFF034-sw1-R : _
lem-comm-push-TOFF034-sw1-R = R007.lem-comm-push-TOFF034-sw1-R sR007
lem-comm-push-BOX⟨4·021⟩-sw1-R : _
lem-comm-push-BOX⟨4·021⟩-sw1-R = R007.lem-comm-push-BOX⟨4·021⟩-sw1-R sR007
sR008 : SR008
sR008 = lem-comm-push-CS04-sw1-R ∷ᵃ lem-comm-push-CS04-sw2-R ∷ᵃ lem-comm-push-BOX⟨0·21⟩-sw0-R ∷ᵃ lem-comm-push-BOX⟨1·20⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨1·230⟩-sw2-R ∷ᵃ lem-comm-push-BOX⟨1·320⟩-sw3-R ∷ᵃ lem-comm-push-BOX⟨1·420⟩-sw2-R ∷ᵃ lem-comm-push-BOX⟨2·03⟩-sw2-R ∷ᵃ lem-comm-push-BOX⟨4·03⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨4·103⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨4·10⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨4·20⟩-sw0-R ∷ᵃ lem-comm-push-CS04-sw0-R ∷ᵃ lem-comm-push-CS14-sw0-R ∷ᵃ lem-comm-push-CSd14-sw0-R ∷ᵃ lem-comm-push-CX04-sw1-R ∷ᵃ lem-comm-push-CX04-sw2-R ∷ᵃ nil
lem-comm-push-TOFF401-sw2-R : _
lem-comm-push-TOFF401-sw2-R = R008.lem-comm-push-TOFF401-sw2-R sR008
lem-comm-push-CCZ024-sw0-R : _
lem-comm-push-CCZ024-sw0-R = R008.lem-comm-push-CCZ024-sw0-R sR008
lem-comm-push-TOFF024-sw0-R : _
lem-comm-push-TOFF024-sw0-R = R008.lem-comm-push-TOFF024-sw0-R sR008
lem-comm-push-TOFF401-sw0-R : _
lem-comm-push-TOFF401-sw0-R = R008.lem-comm-push-TOFF401-sw0-R sR008
lem-comm-push-BOX⟨1·4203⟩-sw1-R : _
lem-comm-push-BOX⟨1·4203⟩-sw1-R = R008.lem-comm-push-BOX⟨1·4203⟩-sw1-R sR008
lem-comm-push-CCZ124-sw0-R : _
lem-comm-push-CCZ124-sw0-R = R008.lem-comm-push-CCZ124-sw0-R sR008
lem-comm-push-TOFF402-sw0-R : _
lem-comm-push-TOFF402-sw0-R = R008.lem-comm-push-TOFF402-sw0-R sR008
lem-comm-push-BOX⟨2·031⟩-sw0-R : _
lem-comm-push-BOX⟨2·031⟩-sw0-R = R008.lem-comm-push-BOX⟨2·031⟩-sw0-R sR008
lem-comm-push-BOX⟨2·130⟩-sw1-R : _
lem-comm-push-BOX⟨2·130⟩-sw1-R = R008.lem-comm-push-BOX⟨2·130⟩-sw1-R sR008
lem-comm-push-BOX⟨2·1430⟩-sw2-R : _
lem-comm-push-BOX⟨2·1430⟩-sw2-R = R008.lem-comm-push-BOX⟨2·1430⟩-sw2-R sR008
lem-comm-push-BOX⟨3·1420⟩-sw3-R : _
lem-comm-push-BOX⟨3·1420⟩-sw3-R = R008.lem-comm-push-BOX⟨3·1420⟩-sw3-R sR008
lem-comm-push-TOFF024-sw3-R : _
lem-comm-push-TOFF024-sw3-R = R008.lem-comm-push-TOFF024-sw3-R sR008
lem-comm-push-BOX⟨4·1320⟩-sw2-R : _
lem-comm-push-BOX⟨4·1320⟩-sw2-R = R008.lem-comm-push-BOX⟨4·1320⟩-sw2-R sR008
lem-comm-push-BOX⟨1·430⟩-sw1-R : _
lem-comm-push-BOX⟨1·430⟩-sw1-R = R008.lem-comm-push-BOX⟨1·430⟩-sw1-R sR008
lem-comm-push-TOFF412-sw0-R : _
lem-comm-push-TOFF412-sw0-R = R008.lem-comm-push-TOFF412-sw0-R sR008
lem-comm-push-BOX⟨2·430⟩-sw0-R : _
lem-comm-push-BOX⟨2·430⟩-sw0-R = R008.lem-comm-push-BOX⟨2·430⟩-sw0-R sR008
lem-comm-push-BOX⟨0·213⟩-sw2-R : _
lem-comm-push-BOX⟨0·213⟩-sw2-R = R008.lem-comm-push-BOX⟨0·213⟩-sw2-R sR008
lem-comm-push-TOFF304-sw3-R : _
lem-comm-push-TOFF304-sw3-R = R008.lem-comm-push-TOFF304-sw3-R sR008
lem-comm-push-BOX⟨0·413⟩-sw1-R : _
lem-comm-push-BOX⟨0·413⟩-sw1-R = R008.lem-comm-push-BOX⟨0·413⟩-sw1-R sR008
sR009 : SR009
sR009 = lem-comm-push-BOX⟨0·312⟩-sw3-R ∷ᵃ lem-comm-push-BOX⟨0·31⟩-sw3-R ∷ᵃ lem-comm-push-BOX⟨0·41⟩-sw3-L ∷ᵃ lem-comm-push-BOX⟨0·42⟩-sw2-R ∷ᵃ lem-comm-push-BOX⟨0·43⟩-sw2-L ∷ᵃ lem-comm-push-BOX⟨4·02⟩-sw2-R ∷ᵃ lem-comm-push-BOX⟨4·03⟩-sw0-R ∷ᵃ lem-comm-push-CCZ014-sw2-L ∷ᵃ lem-comm-push-CCZ024-sw0-L ∷ᵃ lem-comm-push-CCZ034-sw0-L ∷ᵃ lem-comm-push-CCZ034-sw1-L ∷ᵃ lem-comm-push-TOFF023-sw3-L ∷ᵃ lem-comm-push-TOFF024-sw0-L ∷ᵃ lem-comm-push-TOFF024-sw3-L ∷ᵃ lem-comm-push-TOFF034-sw0-L ∷ᵃ lem-comm-push-TOFF034-sw1-L ∷ᵃ lem-comm-push-TOFF204-sw0-L ∷ᵃ lem-comm-push-TOFF304-sw0-L ∷ᵃ lem-comm-push-TOFF304-sw1-L ∷ᵃ lem-comm-push-TOFF401-sw2-L ∷ᵃ lem-comm-push-TOFF402-sw0-L ∷ᵃ lem-comm-push-BOX⟨0·123⟩-sw0-L ∷ᵃ lem-comm-push-BOX⟨0·213⟩-sw1-L ∷ᵃ lem-comm-push-BOX⟨1·023⟩-sw2-L ∷ᵃ lem-comm-push-BOX⟨1·032⟩-sw1-L ∷ᵃ lem-comm-push-BOX⟨1·032⟩-sw2-R ∷ᵃ lem-comm-push-BOX⟨2·031⟩-sw1-R ∷ᵃ lem-comm-push-CCZ014-sw0-L ∷ᵃ lem-comm-push-CCZ014-sw2-R ∷ᵃ lem-comm-push-CCZ023-sw3-L ∷ᵃ lem-comm-push-CCZ024-sw3-L ∷ᵃ lem-comm-push-TOFF014-sw2-L ∷ᵃ lem-comm-push-TOFF014-sw2-R ∷ᵃ lem-comm-push-TOFF104-sw0-L ∷ᵃ lem-comm-push-TOFF104-sw2-L ∷ᵃ lem-comm-push-TOFF203-sw3-L ∷ᵃ lem-comm-push-TOFF204-sw3-L ∷ᵃ lem-comm-push-TOFF302-sw3-L ∷ᵃ lem-comm-push-TOFF402-sw3-L ∷ᵃ lem-comm-push-TOFF403-sw0-L ∷ᵃ lem-comm-push-TOFF403-sw1-L ∷ᵃ lem-comm-push-BOX⟨0·123⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨1·023⟩-sw0-R ∷ᵃ lem-comm-push-BOX⟨2·031⟩-sw2-R ∷ᵃ lem-comm-push-BOX⟨2·4103⟩-sw1-L ∷ᵃ lem-comm-push-BOX⟨3·021⟩-sw2-L ∷ᵃ lem-comm-push-BOX⟨4·012⟩-sw1-L ∷ᵃ lem-comm-push-BOX⟨4·021⟩-sw1-R ∷ᵃ lem-comm-push-CCZ014-sw0-R ∷ᵃ lem-comm-push-CCZ023-sw3-R ∷ᵃ lem-comm-push-CCZ034-sw1-R ∷ᵃ lem-comm-push-CCZ034-sw3-R ∷ᵃ lem-comm-push-CCZ124-sw0-L ∷ᵃ lem-comm-push-TOFF014-sw0-R ∷ᵃ lem-comm-push-TOFF034-sw1-R ∷ᵃ lem-comm-push-TOFF302-sw3-R ∷ᵃ lem-comm-push-TOFF401-sw0-L ∷ᵃ lem-comm-push-TOFF412-sw0-L ∷ᵃ lem-comm-push-BOX⟨0·213⟩-sw2-R ∷ᵃ lem-comm-push-BOX⟨0·413⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨1·4203⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨1·430⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨2·031⟩-sw0-R ∷ᵃ lem-comm-push-BOX⟨2·130⟩-sw1-R ∷ᵃ lem-comm-push-BOX⟨2·1430⟩-sw2-R ∷ᵃ lem-comm-push-BOX⟨2·430⟩-sw0-R ∷ᵃ lem-comm-push-BOX⟨3·1420⟩-sw3-R ∷ᵃ lem-comm-push-BOX⟨4·1320⟩-sw2-R ∷ᵃ lem-comm-push-CCZ024-sw0-R ∷ᵃ lem-comm-push-CCZ124-sw0-R ∷ᵃ lem-comm-push-TOFF024-sw0-R ∷ᵃ lem-comm-push-TOFF024-sw3-R ∷ᵃ lem-comm-push-TOFF304-sw3-R ∷ᵃ lem-comm-push-TOFF401-sw0-R ∷ᵃ lem-comm-push-TOFF401-sw2-R ∷ᵃ lem-comm-push-TOFF402-sw0-R ∷ᵃ lem-comm-push-TOFF412-sw0-R ∷ᵃ nil
lem-comm-TOFF023-CSd14 : _
lem-comm-TOFF023-CSd14 = R009.lem-comm-TOFF023-CSd14 sR009
lem-comm-TOFF203-CSd14 : _
lem-comm-TOFF203-CSd14 = R009.lem-comm-TOFF203-CSd14 sR009
lem-comm-CCZ023-CK41 : _
lem-comm-CCZ023-CK41 = R009.lem-comm-CCZ023-CK41 sR009
lem-comm-TOFF023-CK41 : _
lem-comm-TOFF023-CK41 = R009.lem-comm-TOFF023-CK41 sR009
lem-comm-TOFF023-CX14 : _
lem-comm-TOFF023-CX14 = R009.lem-comm-TOFF023-CX14 sR009
lem-comm-TOFF302-CSd14 : _
lem-comm-TOFF302-CSd14 = R009.lem-comm-TOFF302-CSd14 sR009
lem-sym-ab : _
lem-sym-ab = D001.lem-sym-ab
lem-cQ-at13243142 : _
lem-cQ-at13243142 = D001.lem-cQ-at13243142
lem-cQ-at13243241 : _
lem-cQ-at13243241 = D001.lem-cQ-at13243241
lem-sym-ab-at2332 : _
lem-sym-ab-at2332 = D001.lem-sym-ab-at2332
lem-sym-ab-at13243142 : _
lem-sym-ab-at13243142 = D001.lem-sym-ab-at13243142
lem-sym-ab-at122331 : _
lem-sym-ab-at122331 = D001.lem-sym-ab-at122331
lem-sym-ab-at13243241 : _
lem-sym-ab-at13243241 = D001.lem-sym-ab-at13243241
lem-sym-ab-at12243143 : _
lem-sym-ab-at12243143 = D001.lem-sym-ab-at12243143
lem-cQ-at14233142 : _
lem-cQ-at14233142 = D001.lem-cQ-at14233142
lem-sym-ab-at13213442 : _
lem-sym-ab-at13213442 = D001.lem-sym-ab-at13213442
lem-sym-ab-at243243 : _
lem-sym-ab-at243243 = D001.lem-sym-ab-at243243
lem-sym-ab-at133441 : _
lem-sym-ab-at133441 = D001.lem-sym-ab-at133441
lem-sym-ab-at12233441 : _
lem-sym-ab-at12233441 = D001.lem-sym-ab-at12233441
lem-sym-ab-at1221 : _
lem-sym-ab-at1221 = D001.lem-sym-ab-at1221
lem-cQ-at021021 : _
lem-cQ-at021021 = D001.lem-cQ-at021021
lem-sym-ab-at233442 : _
lem-sym-ab-at233442 = D001.lem-sym-ab-at233442
lem-cQ-at03102132 : _
lem-cQ-at03102132 = D001.lem-cQ-at03102132
lem-sym-ab-at14233142 : _
lem-sym-ab-at14233142 = D001.lem-sym-ab-at14233142
lem-cQ-at0410213243 : _
lem-cQ-at0410213243 = D001.lem-cQ-at0410213243
lem-cQ-at04203243 : _
lem-cQ-at04203243 = D001.lem-cQ-at04203243
lem-sym-ab-at04203243 : _
lem-sym-ab-at04203243 = D001.lem-sym-ab-at04203243
lem-sym-ab-at0310243142 : _
lem-sym-ab-at0310243142 = D001.lem-sym-ab-at0310243142
lem-sym-ab-at0314203142 : _
lem-sym-ab-at0314203142 = D001.lem-sym-ab-at0314203142
lem-sym-ab-at0410213243 : _
lem-sym-ab-at0410213243 = D001.lem-sym-ab-at0410213243
lem-sym-ab-at03102132 : _
lem-sym-ab-at03102132 = D001.lem-sym-ab-at03102132
lem-cQ-at032032 : _
lem-cQ-at032032 = D001.lem-cQ-at032032
lem-sym-ab-at032032 : _
lem-sym-ab-at032032 = D001.lem-sym-ab-at032032
lem-sym-ab-at0210243143 : _
lem-sym-ab-at0210243143 = D001.lem-sym-ab-at0210243143
lem-nat-SWbc-at0214203143 : _
lem-nat-SWbc-at0214203143 = D001.lem-nat-SWbc-at0214203143
lem-nat-SWbc-at122441 : _
lem-nat-SWbc-at122441 = D001.lem-nat-SWbc-at122441
lem-nat-SWbc-at14213243 : _
lem-nat-SWbc-at14213243 = D001.lem-nat-SWbc-at14213243
lem-cQ-at0210213443 : _
lem-cQ-at0210213443 = D001.lem-cQ-at0210213443
lem-sym-ab-at122441 : _
lem-sym-ab-at122441 = D001.lem-sym-ab-at122441
lem-cQ-at14233241 : _
lem-cQ-at14233241 = D001.lem-cQ-at14233241
lem-nat-SWbc-at0314213042 : _
lem-nat-SWbc-at0314213042 = D001.lem-nat-SWbc-at0314213042
lem-sym-ab-at0210233441 : _
lem-sym-ab-at0210233441 = D001.lem-sym-ab-at0210233441
lem-sym-ab-at0213203441 : _
lem-sym-ab-at0213203441 = D001.lem-sym-ab-at0213203441
lem-nat-SWbc-at0314203142 : _
lem-nat-SWbc-at0314203142 = D001.lem-nat-SWbc-at0314203142
lem-nat-SWbc-at0214213043 : _
lem-nat-SWbc-at0214213043 = D001.lem-nat-SWbc-at0214213043
lem-sym-ab-at0214203143 : _
lem-sym-ab-at0214203143 = D001.lem-sym-ab-at0214203143
lem-nat-SWbc-at1331 : _
lem-nat-SWbc-at1331 = D001.lem-nat-SWbc-at1331
lem-sym-ab-at0312213440 : _
lem-sym-ab-at0312213440 = D001.lem-sym-ab-at0312213440
lem-sym-ab-at033440 : _
lem-sym-ab-at033440 = D001.lem-sym-ab-at033440
lem-nat-SWbc-at132132 : _
lem-nat-SWbc-at132132 = D001.lem-nat-SWbc-at132132
lem-sym-ab-at1331 : _
lem-sym-ab-at1331 = D002.lem-sym-ab-at1331
lem-sym-ab-at0220 : _
lem-sym-ab-at0220 = D002.lem-sym-ab-at0220
lem-sym-ab-at14233241 : _
lem-sym-ab-at14233241 = D002.lem-sym-ab-at14233241
lem-sym-ab-at021021 : _
lem-sym-ab-at021021 = D002.lem-sym-ab-at021021
lem-cQ-at0220 : _
lem-cQ-at0220 = D002.lem-cQ-at0220
lem-cQ-at0213243140 : _
lem-cQ-at0213243140 = D002.lem-cQ-at0213243140
lem-sym-ab-at0213213440 : _
lem-sym-ab-at0213213440 = D002.lem-sym-ab-at0213213440
lem-sym-ab-at02233440 : _
lem-sym-ab-at02233440 = D002.lem-sym-ab-at02233440
lem-nat-SWbc-at12233441 : _
lem-nat-SWbc-at12233441 = D002.lem-nat-SWbc-at12233441
lem-sym-ab-at14213243 : _
lem-sym-ab-at14213243 = D002.lem-sym-ab-at14213243
lem-sym-ab-at132132 : _
lem-sym-ab-at132132 = D002.lem-sym-ab-at132132
lem-nat-SWbc-at02233440 : _
lem-nat-SWbc-at02233440 = D002.lem-nat-SWbc-at02233440
lem-nat-SWbc-at022440 : _
lem-nat-SWbc-at022440 = D002.lem-nat-SWbc-at022440
lem-nat-SWbc-at0210233441 : _
lem-nat-SWbc-at0210233441 = D002.lem-nat-SWbc-at0210233441
lem-nat-SWbc-at02102441 : _
lem-nat-SWbc-at02102441 = D002.lem-nat-SWbc-at02102441
lem-nat-SWbc-at233442 : _
lem-nat-SWbc-at233442 = D002.lem-nat-SWbc-at233442
lem-nat-SWbc-at2442 : _
lem-nat-SWbc-at2442 = D002.lem-nat-SWbc-at2442
lem-nat-SWbc-at143143 : _
lem-nat-SWbc-at143143 = D002.lem-nat-SWbc-at143143
lem-nat-SWbc-at033440 : _
lem-nat-SWbc-at033440 = D002.lem-nat-SWbc-at033440
lem-nat-SWbc-at03243240 : _
lem-nat-SWbc-at03243240 = D002.lem-nat-SWbc-at03243240
lem-nat-SWbc-at03103441 : _
lem-nat-SWbc-at03103441 = D002.lem-nat-SWbc-at03103441
lem-nat-SWbc-at0310243241 : _
lem-nat-SWbc-at0310243241 = D002.lem-nat-SWbc-at0310243241
lem-cQ-at0310213442 : _
lem-cQ-at0310213442 = D002.lem-cQ-at0310213442
lem-cQ-at0214233041 : _
lem-cQ-at0214233041 = D002.lem-cQ-at0214233041
lem-sym-ab-at0213243041 : _
lem-sym-ab-at0213243041 = D002.lem-sym-ab-at0213243041
lem-nat-SWbc-at02132130 : _
lem-nat-SWbc-at02132130 = D002.lem-nat-SWbc-at02132130
lem-nat-SWbc-at02132031 : _
lem-nat-SWbc-at02132031 = D002.lem-nat-SWbc-at02132031
lem-cQ-at0213243041 : _
lem-cQ-at0213243041 = D002.lem-cQ-at0213243041
lem-nat-SWbc-at03122130 : _
lem-nat-SWbc-at03122130 = D002.lem-nat-SWbc-at03122130
lem-nat-SWbc-at03122031 : _
lem-nat-SWbc-at03122031 = D002.lem-nat-SWbc-at03122031
sD004 : SD004
sD004 = (λ c → lem-comm-CX02-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-CX04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CX12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX14-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CX21-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX24-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-CX31-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX32-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX42-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-SWAP02-BOX⟨4·13⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP13-BOX⟨0·24⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP13-BOX⟨0·42⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP14-BOX⟨0·23⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP14-BOX⟨0·32⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP23-BOX⟨0·14⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP24-BOX⟨0·31⟩ (lit c)) ∷ᵃ (λ c → lem-comm-CX03-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CX30-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CX40-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CX41-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-SWAP02-BOX⟨3·14⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP12-BOX⟨3·04⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP14-BOX⟨2·03⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP14-BOX⟨2·30⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP14-BOX⟨3·20⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP23-BOX⟨0·41⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP24-BOX⟨0·13⟩ (lit c)) ∷ᵃ lem-cQ-at021021 ∷ᵃ lem-cQ-at0210213443 ∷ᵃ lem-cQ-at03102132 ∷ᵃ lem-cQ-at032032 ∷ᵃ lem-cQ-at0410213243 ∷ᵃ lem-cQ-at04203243 ∷ᵃ lem-cQ-at13243142 ∷ᵃ lem-cQ-at13243241 ∷ᵃ lem-cQ-at14233142 ∷ᵃ lem-cQ-at14233241 ∷ᵃ lem-sym-ab ∷ᵃ lem-sym-ab-at03102132 ∷ᵃ lem-cQ-at0213243140 ∷ᵃ lem-cQ-at0220 ∷ᵃ nil
lem-cQ : _
lem-cQ = D004.lem-cQ sD004
lem-cQ-at0210243143 : _
lem-cQ-at0210243143 = D004.lem-cQ-at0210243143 sD004
lem-cQ-at243243 : _
lem-cQ-at243243 = D004.lem-cQ-at243243 sD004
lem-cQ-at122441 : _
lem-cQ-at122441 = D004.lem-cQ-at122441 sD004
lem-nat-SWbc : _
lem-nat-SWbc = D004.lem-nat-SWbc sD004
lem-box-tQ-at13243142 : _
lem-box-tQ-at13243142 = D004.lem-box-tQ-at13243142 sD004
lem-cQ-at1221 : _
lem-cQ-at1221 = D004.lem-cQ-at1221 sD004
lem-nat-SWbc-at1221 : _
lem-nat-SWbc-at1221 = D004.lem-nat-SWbc-at1221 sD004
lem-box-tQ-at13243241 : _
lem-box-tQ-at13243241 = D004.lem-box-tQ-at13243241 sD004
lem-cQ-at2332 : _
lem-cQ-at2332 = D004.lem-cQ-at2332 sD004
lem-cQ-at12243143 : _
lem-cQ-at12243143 = D004.lem-cQ-at12243143 sD004
lem-nat-SWbc-at13243142 : _
lem-nat-SWbc-at13243142 = D004.lem-nat-SWbc-at13243142 sD004
lem-cQ-at122331 : _
lem-cQ-at122331 = D004.lem-cQ-at122331 sD004
lem-nat-SWbc-at13243241 : _
lem-nat-SWbc-at13243241 = D004.lem-nat-SWbc-at13243241 sD004
lem-cQ-at132132 : _
lem-cQ-at132132 = D004.lem-cQ-at132132 sD004
lem-nat-SWbc-at12243143 : _
lem-nat-SWbc-at12243143 = D004.lem-nat-SWbc-at12243143 sD004
lem-box-tQ-at14233142 : _
lem-box-tQ-at14233142 = D004.lem-box-tQ-at14233142 sD004
lem-nat-SWbc-at14233142 : _
lem-nat-SWbc-at14233142 = D004.lem-nat-SWbc-at14233142 sD004
lem-tP-at14233142 : _
lem-tP-at14233142 = D004.lem-tP-at14233142 sD004
lem-cQ-at3443 : _
lem-cQ-at3443 = D004.lem-cQ-at3443 sD004
lem-cQ-at13213442 : _
lem-cQ-at13213442 = D004.lem-cQ-at13213442 sD004
lem-cQ-at1441 : _
lem-cQ-at1441 = D004.lem-cQ-at1441 sD004
lem-cQ-at1331 : _
lem-cQ-at1331 = D004.lem-cQ-at1331 sD004
lem-cQ-at2442 : _
lem-cQ-at2442 = D004.lem-cQ-at2442 sD004
lem-cQ-at12233441 : _
lem-cQ-at12233441 = D004.lem-cQ-at12233441 sD004
lem-cQ-at0110 : _
lem-cQ-at0110 = D004.lem-cQ-at0110 sD004
lem-cQ-at133441 : _
lem-cQ-at133441 = D004.lem-cQ-at133441 sD004
lem-nat-SWbc-at133441 : _
lem-nat-SWbc-at133441 = D004.lem-nat-SWbc-at133441 sD004
lem-tP-at13243241 : _
lem-tP-at13243241 = D004.lem-tP-at13243241 sD004
lem-cQ-at233442 : _
lem-cQ-at233442 = D004.lem-cQ-at233442 sD004
lem-tP-at021021 : _
lem-tP-at021021 = D004.lem-tP-at021021 sD004
lem-nat-SWbc-at13213442 : _
lem-nat-SWbc-at13213442 = D004.lem-nat-SWbc-at13213442 sD004
lem-tP-at13243142 : _
lem-tP-at13243142 = D004.lem-tP-at13243142 sD004
lem-tP-at03102132 : _
lem-tP-at03102132 = D004.lem-tP-at03102132 sD004
lem-tP-at0410213243 : _
lem-tP-at0410213243 = D004.lem-tP-at0410213243 sD004
lem-cQ-at043043 : _
lem-cQ-at043043 = D004.lem-cQ-at043043 sD004
lem-cQ-at0330 : _
lem-cQ-at0330 = D004.lem-cQ-at0330 sD004
lem-nat-SWbc-at043043 : _
lem-nat-SWbc-at043043 = D004.lem-nat-SWbc-at043043 sD004
lem-tP-at04203243 : _
lem-tP-at04203243 = D004.lem-tP-at04203243 sD004
lem-cQ-at0310243142 : _
lem-cQ-at0310243142 = D004.lem-cQ-at0310243142 sD004
lem-box-tQ-at0410213243 : _
lem-box-tQ-at0410213243 = D004.lem-box-tQ-at0410213243 sD004
lem-cQ-at0314203142 : _
lem-cQ-at0314203142 = D004.lem-cQ-at0314203142 sD004
lem-box-tQ-at04203243 : _
lem-box-tQ-at04203243 = D004.lem-box-tQ-at04203243 sD004
lem-nat-SWbc-at04203243 : _
lem-nat-SWbc-at04203243 = D004.lem-nat-SWbc-at04203243 sD004
lem-box-tQ-at032032 : _
lem-box-tQ-at032032 = D004.lem-box-tQ-at032032 sD004
lem-nat-SWbc-at032032 : _
lem-nat-SWbc-at032032 = D004.lem-nat-SWbc-at032032 sD004
lem-nat-SWbc-at0330 : _
lem-nat-SWbc-at0330 = D004.lem-nat-SWbc-at0330 sD004
lem-cQ-at0214203143 : _
lem-cQ-at0214203143 = D004.lem-cQ-at0214203143 sD004
lem-cQ-at0214213043 : _
lem-cQ-at0214213043 = D004.lem-cQ-at0214213043 sD004
lem-cQ-at0210233441 : _
lem-cQ-at0210233441 = D004.lem-cQ-at0210233441 sD004
lem-cQ-at14213243 : _
lem-cQ-at14213243 = D004.lem-cQ-at14213243 sD004
lem-cQ-at143143 : _
lem-cQ-at143143 = D004.lem-cQ-at143143 sD004
lem-nat-SWbc-at0210243143 : _
lem-nat-SWbc-at0210243143 = D004.lem-nat-SWbc-at0210243143 sD004
lem-tP-at0210213443 : _
lem-tP-at0210213443 = D004.lem-tP-at0210213443 sD004
lem-nat-SWbc-at243243 : _
lem-nat-SWbc-at243243 = D004.lem-nat-SWbc-at243243 sD004
lem-nat-SWbc-at1441 : _
lem-nat-SWbc-at1441 = D004.lem-nat-SWbc-at1441 sD004
lem-box-tQ-at14233241 : _
lem-box-tQ-at14233241 = D004.lem-box-tQ-at14233241 sD004
lem-tP-at14233241 : _
lem-tP-at14233241 = D004.lem-tP-at14233241 sD004
lem-cQ-at12213443 : _
lem-cQ-at12213443 = D004.lem-cQ-at12213443 sD004
lem-cQ-at0314213042 : _
lem-cQ-at0314213042 = D004.lem-cQ-at0314213042 sD004
lem-cQ-at0213203441 : _
lem-cQ-at0213203441 = D004.lem-cQ-at0213203441 sD004
lem-tP-at032032 : _
lem-tP-at032032 = D004.lem-tP-at032032 sD004
lem-cQ-at0312243140 : _
lem-cQ-at0312243140 = D004.lem-cQ-at0312243140 sD004
lem-nat-SWbc-at0312243140 : _
lem-nat-SWbc-at0312243140 = D004.lem-nat-SWbc-at0312243140 sD004
lem-cQ-at033440 : _
lem-cQ-at033440 = D004.lem-cQ-at033440 sD004
lem-cQ-at0312213440 : _
lem-cQ-at0312213440 = D004.lem-cQ-at0312213440 sD004
lem-nat-SWbc-at0312213440 : _
lem-nat-SWbc-at0312213440 = D004.lem-nat-SWbc-at0312213440 sD004
lem-cQ-at022330 : _
lem-cQ-at022330 = D004.lem-cQ-at022330 sD004
lem-box-tQ-at0220 : _
lem-box-tQ-at0220 = D004.lem-box-tQ-at0220 sD004
lem-tP-at0220 : _
lem-tP-at0220 = D004.lem-tP-at0220 sD004
lem-box-tQ-at0213243140 : _
lem-box-tQ-at0213243140 = D004.lem-box-tQ-at0213243140 sD004
lem-nat-SWbc-at0213243140 : _
lem-nat-SWbc-at0213243140 = D004.lem-nat-SWbc-at0213243140 sD004
lem-cQ-at02233440 : _
lem-cQ-at02233440 = D004.lem-cQ-at02233440 sD004
lem-cQ-at0213213440 : _
lem-cQ-at0213213440 = D004.lem-cQ-at0213213440 sD004
lem-nat-SWbc-at0213213440 : _
lem-nat-SWbc-at0213213440 = D004.lem-nat-SWbc-at0213213440 sD004
lem-tP-at0213243140 : _
lem-tP-at0213243140 = D004.lem-tP-at0213243140 sD004
lem-nat-SWbc-at122331 : _
lem-nat-SWbc-at122331 = D004.lem-nat-SWbc-at122331 sD004
lem-nat-SWbc-at2332 : _
lem-nat-SWbc-at2332 = D004.lem-nat-SWbc-at2332 sD004
lem-box-tQ-at0210213443 : _
lem-box-tQ-at0210213443 = D004.lem-box-tQ-at0210213443 sD004
lem-box-perm-2134-at03102132 : _
lem-box-perm-2134-at03102132 = D004.lem-box-perm-2134-at03102132 sD004
lem-box-tQ-at03102132 : _
lem-box-tQ-at03102132 = D004.lem-box-tQ-at03102132 sD004
lem-nat-SWbc-at03102132 : _
lem-nat-SWbc-at03102132 = D004.lem-nat-SWbc-at03102132 sD004
lem-cQ-at022440 : _
lem-cQ-at022440 = D004.lem-cQ-at022440 sD004
lem-cQ-at02102441 : _
lem-cQ-at02102441 = D004.lem-cQ-at02102441 sD004
sD006 : SD006
sD006 = (λ c → lem-comm-CS12-TOFF034 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-TOFF034 (lit c)) ∷ᵃ (λ c → lem-comm-CZ04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CZ12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CZ12-TOFF034 (lit c)) ∷ᵃ (λ c → lem-comm-CZ13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CZ14-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CZ23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CZ24-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF034-CSd12 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF301-CSd24 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF401-CSd23 (lit c)) ∷ᵃ (λ c → lem-comm-CS23-TOFF401 (lit c)) ∷ᵃ (λ c → lem-comm-CS24-TOFF301 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-TOFF401 (lit c)) ∷ᵃ (λ c → lem-comm-CSd24-TOFF301 (lit c)) ∷ᵃ (λ c → lem-comm-CZ03-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CZ24-TOFF301 (lit c)) ∷ᵃ (λ c → lem-comm-SWAP03-BOX⟨2·14⟩ (lit c)) ∷ᵃ lem-box-tQ-at0213243140 ∷ᵃ lem-box-tQ-at0220 ∷ᵃ lem-box-tQ-at032032 ∷ᵃ lem-box-tQ-at04203243 ∷ᵃ lem-box-tQ-at13243142 ∷ᵃ lem-box-tQ-at13243241 ∷ᵃ lem-box-tQ-at14233142 ∷ᵃ lem-box-tQ-at14233241 ∷ᵃ lem-cQ ∷ᵃ lem-cQ-at0110 ∷ᵃ lem-cQ-at0210233441 ∷ᵃ lem-cQ-at0210243143 ∷ᵃ lem-cQ-at0213203441 ∷ᵃ lem-cQ-at0214203143 ∷ᵃ lem-cQ-at0214213043 ∷ᵃ lem-cQ-at022330 ∷ᵃ lem-cQ-at0310243142 ∷ᵃ lem-cQ-at0312213440 ∷ᵃ lem-cQ-at0312243140 ∷ᵃ lem-cQ-at0314203142 ∷ᵃ lem-cQ-at0314213042 ∷ᵃ lem-cQ-at0330 ∷ᵃ lem-cQ-at033440 ∷ᵃ lem-cQ-at043043 ∷ᵃ lem-cQ-at1221 ∷ᵃ lem-cQ-at12213443 ∷ᵃ lem-cQ-at122331 ∷ᵃ lem-cQ-at12233441 ∷ᵃ lem-cQ-at12243143 ∷ᵃ lem-cQ-at122441 ∷ᵃ lem-cQ-at132132 ∷ᵃ lem-cQ-at13213442 ∷ᵃ lem-cQ-at1331 ∷ᵃ lem-cQ-at133441 ∷ᵃ lem-cQ-at14213243 ∷ᵃ lem-cQ-at143143 ∷ᵃ lem-cQ-at1441 ∷ᵃ lem-cQ-at2332 ∷ᵃ lem-cQ-at233442 ∷ᵃ lem-cQ-at243243 ∷ᵃ lem-cQ-at2442 ∷ᵃ lem-cQ-at3443 ∷ᵃ lem-tP-at021021 ∷ᵃ lem-tP-at0210213443 ∷ᵃ lem-tP-at0220 ∷ᵃ lem-tP-at03102132 ∷ᵃ lem-tP-at032032 ∷ᵃ lem-tP-at0410213243 ∷ᵃ lem-tP-at04203243 ∷ᵃ lem-tP-at13243142 ∷ᵃ lem-tP-at13243241 ∷ᵃ lem-tP-at14233142 ∷ᵃ lem-tP-at14233241 ∷ᵃ nil
lem-tP : _
lem-tP = D006.lem-tP sD006
lem-box-tQ : _
lem-box-tQ = D006.lem-box-tQ sD006
lem-tP-at0210243143 : _
lem-tP-at0210243143 = D006.lem-tP-at0210243143 sD006
lem-box-tQ-at0210243143 : _
lem-box-tQ-at0210243143 = D006.lem-box-tQ-at0210243143 sD006
lem-tP-at243243 : _
lem-tP-at243243 = D006.lem-tP-at243243 sD006
lem-box-tQ-at243243 : _
lem-box-tQ-at243243 = D006.lem-box-tQ-at243243 sD006
lem-tP-at122441 : _
lem-tP-at122441 = D006.lem-tP-at122441 sD006
lem-box-tQ-at122441 : _
lem-box-tQ-at122441 = D006.lem-box-tQ-at122441 sD006
lem-box-tQ-at1221 : _
lem-box-tQ-at1221 = D006.lem-box-tQ-at1221 sD006
lem-tP-at1221 : _
lem-tP-at1221 = D006.lem-tP-at1221 sD006
lem-box-tQ-at2332 : _
lem-box-tQ-at2332 = D006.lem-box-tQ-at2332 sD006
lem-tP-at2332 : _
lem-tP-at2332 = D006.lem-tP-at2332 sD006
lem-box-tQ-at12243143 : _
lem-box-tQ-at12243143 = D006.lem-box-tQ-at12243143 sD006
lem-CXbc-box-at13243142 : _
lem-CXbc-box-at13243142 = D006.lem-CXbc-box-at13243142 sD006
lem-CXcb-box-at13243142 : _
lem-CXcb-box-at13243142 = D006.lem-CXcb-box-at13243142 sD006
lem-box-tQ-at122331 : _
lem-box-tQ-at122331 = D006.lem-box-tQ-at122331 sD006
lem-tP-at122331 : _
lem-tP-at122331 = D006.lem-tP-at122331 sD006
lem-CXbc-box-at13243241 : _
lem-CXbc-box-at13243241 = D006.lem-CXbc-box-at13243241 sD006
lem-CXcb-box-at13243241 : _
lem-CXcb-box-at13243241 = D006.lem-CXcb-box-at13243241 sD006
lem-box-tQ-at132132 : _
lem-box-tQ-at132132 = D006.lem-box-tQ-at132132 sD006
lem-tP-at132132 : _
lem-tP-at132132 = D006.lem-tP-at132132 sD006
lem-CXbc-box-at14233142 : _
lem-CXbc-box-at14233142 = D006.lem-CXbc-box-at14233142 sD006
lem-CXcb-box-at14233142 : _
lem-CXcb-box-at14233142 = D006.lem-CXcb-box-at14233142 sD006
lem-P-box-at14233142 : _
lem-P-box-at14233142 = D006.lem-P-box-at14233142 sD006
lem-VPQ-at14233142 : _
lem-VPQ-at14233142 = D006.lem-VPQ-at14233142 sD006
lem-box-tQ-at3443 : _
lem-box-tQ-at3443 = D006.lem-box-tQ-at3443 sD006
lem-box-tQ-at13213442 : _
lem-box-tQ-at13213442 = D006.lem-box-tQ-at13213442 sD006
lem-tP-at13213442 : _
lem-tP-at13213442 = D006.lem-tP-at13213442 sD006
lem-box-tQ-at1441 : _
lem-box-tQ-at1441 = D006.lem-box-tQ-at1441 sD006
lem-box-tQ-at1331 : _
lem-box-tQ-at1331 = D006.lem-box-tQ-at1331 sD006
lem-tP-at1331 : _
lem-tP-at1331 = D006.lem-tP-at1331 sD006
lem-box-tQ-at2442 : _
lem-box-tQ-at2442 = D006.lem-box-tQ-at2442 sD006
lem-box-tQ-at12233441 : _
lem-box-tQ-at12233441 = D006.lem-box-tQ-at12233441 sD006
lem-tP-at0110 : _
lem-tP-at0110 = D006.lem-tP-at0110 sD006
lem-box-tQ-at133441 : _
lem-box-tQ-at133441 = D006.lem-box-tQ-at133441 sD006
lem-P-box-at13243241 : _
lem-P-box-at13243241 = D006.lem-P-box-at13243241 sD006
lem-VPQ-at13243241 : _
lem-VPQ-at13243241 = D006.lem-VPQ-at13243241 sD006
lem-box-tQ-at233442 : _
lem-box-tQ-at233442 = D006.lem-box-tQ-at233442 sD006
lem-VPQ-at021021 : _
lem-VPQ-at021021 = D006.lem-VPQ-at021021 sD006
lem-P-box-at13243142 : _
lem-P-box-at13243142 = D006.lem-P-box-at13243142 sD006
lem-VPQ-at13243142 : _
lem-VPQ-at13243142 = D006.lem-VPQ-at13243142 sD006
lem-VPQ-at03102132 : _
lem-VPQ-at03102132 = D006.lem-VPQ-at03102132 sD006
lem-tP-at3443 : _
lem-tP-at3443 = D006.lem-tP-at3443 sD006
lem-VPQ-at0410213243 : _
lem-VPQ-at0410213243 = D006.lem-VPQ-at0410213243 sD006
lem-box-tQ-at043043 : _
lem-box-tQ-at043043 = D006.lem-box-tQ-at043043 sD006
lem-tP-at043043 : _
lem-tP-at043043 = D006.lem-tP-at043043 sD006
lem-box-tQ-at0330 : _
lem-box-tQ-at0330 = D006.lem-box-tQ-at0330 sD006
lem-VPQ-at04203243 : _
lem-VPQ-at04203243 = D006.lem-VPQ-at04203243 sD006
lem-tP-at0330 : _
lem-tP-at0330 = D006.lem-tP-at0330 sD006
lem-box-tQ-at0310243142 : _
lem-box-tQ-at0310243142 = D006.lem-box-tQ-at0310243142 sD006
lem-tP-at0314203142 : _
lem-tP-at0314203142 = D006.lem-tP-at0314203142 sD006
lem-tP-at0310243142 : _
lem-tP-at0310243142 = D006.lem-tP-at0310243142 sD006
lem-CXbc-box-at04203243 : _
lem-CXbc-box-at04203243 = D006.lem-CXbc-box-at04203243 sD006
lem-CXcb-box-at04203243 : _
lem-CXcb-box-at04203243 = D006.lem-CXcb-box-at04203243 sD006
lem-CXbc-box-at032032 : _
lem-CXbc-box-at032032 = D006.lem-CXbc-box-at032032 sD006
lem-CXcb-box-at032032 : _
lem-CXcb-box-at032032 = D006.lem-CXcb-box-at032032 sD006
lem-box-tQ-at0214203143 : _
lem-box-tQ-at0214203143 = D006.lem-box-tQ-at0214203143 sD006
lem-box-tQ-at0214213043 : _
lem-box-tQ-at0214213043 = D006.lem-box-tQ-at0214213043 sD006
lem-tP-at0214213043 : _
lem-tP-at0214213043 = D006.lem-tP-at0214213043 sD006
lem-box-tQ-at0210233441 : _
lem-box-tQ-at0210233441 = D006.lem-box-tQ-at0210233441 sD006
lem-tP-at0210233441 : _
lem-tP-at0210233441 = D006.lem-tP-at0210233441 sD006
lem-tP-at12233441 : _
lem-tP-at12233441 = D006.lem-tP-at12233441 sD006
lem-box-tQ-at14213243 : _
lem-box-tQ-at14213243 = D006.lem-box-tQ-at14213243 sD006
lem-box-tQ-at143143 : _
lem-box-tQ-at143143 = D006.lem-box-tQ-at143143 sD006
lem-tP-at143143 : _
lem-tP-at143143 = D006.lem-tP-at143143 sD006
lem-tP-at233442 : _
lem-tP-at233442 = D006.lem-tP-at233442 sD006
lem-VPQ-at0210213443 : _
lem-VPQ-at0210213443 = D006.lem-VPQ-at0210213443 sD006
lem-P-box-at14233241 : _
lem-P-box-at14233241 = D006.lem-P-box-at14233241 sD006
lem-VPQ-at14233241 : _
lem-VPQ-at14233241 = D006.lem-VPQ-at14233241 sD006
lem-box-tQ-at12213443 : _
lem-box-tQ-at12213443 = D006.lem-box-tQ-at12213443 sD006
lem-tP-at12213443 : _
lem-tP-at12213443 = D006.lem-tP-at12213443 sD006
lem-box-tQ-at0314213042 : _
lem-box-tQ-at0314213042 = D006.lem-box-tQ-at0314213042 sD006
lem-tP-at0213203441 : _
lem-tP-at0213203441 = D006.lem-tP-at0213203441 sD006
lem-box-tQ-at0314203142 : _
lem-box-tQ-at0314203142 = D006.lem-box-tQ-at0314203142 sD006
lem-tP-at0314213042 : _
lem-tP-at0314213042 = D006.lem-tP-at0314213042 sD006
lem-P-box-at032032 : _
lem-P-box-at032032 = D006.lem-P-box-at032032 sD006
lem-VPQ-at032032 : _
lem-VPQ-at032032 = D006.lem-VPQ-at032032 sD006
lem-box-tQ-at0312243140 : _
lem-box-tQ-at0312243140 = D006.lem-box-tQ-at0312243140 sD006
lem-box-tQ-at033440 : _
lem-box-tQ-at033440 = D006.lem-box-tQ-at033440 sD006
lem-box-tQ-at0312213440 : _
lem-box-tQ-at0312213440 = D006.lem-box-tQ-at0312213440 sD006
lem-tP-at0312243140 : _
lem-tP-at0312243140 = D006.lem-tP-at0312243140 sD006
lem-box-tQ-at022330 : _
lem-box-tQ-at022330 = D006.lem-box-tQ-at022330 sD006
lem-nat-SWbc-at022330 : _
lem-nat-SWbc-at022330 = D006.lem-nat-SWbc-at022330 sD006
lem-P-box-at0220 : _
lem-P-box-at0220 = D006.lem-P-box-at0220 sD006
lem-VPQ-at0220 : _
lem-VPQ-at0220 = D006.lem-VPQ-at0220 sD006
lem-CXbc-box-at0213243140 : _
lem-CXbc-box-at0213243140 = D006.lem-CXbc-box-at0213243140 sD006
lem-CXcb-box-at0213243140 : _
lem-CXcb-box-at0213243140 = D006.lem-CXcb-box-at0213243140 sD006
lem-comm-TOFF403-CSd12 : _
lem-comm-TOFF403-CSd12 = R004.lem-comm-TOFF403-CSd12
lem-comm-CS02-TOFF413 : _
lem-comm-CS02-TOFF413 = R004.lem-comm-CS02-TOFF413
lem-comm-CS12-TOFF403 : _
lem-comm-CS12-TOFF403 = R004.lem-comm-CS12-TOFF403
lem-comm-CZ02-TOFF413 : _
lem-comm-CZ02-TOFF413 = R004.lem-comm-CZ02-TOFF413
lem-comm-SWAP13-BOX⟨4·20⟩ : _
lem-comm-SWAP13-BOX⟨4·20⟩ = R004.lem-comm-SWAP13-BOX⟨4·20⟩
lem-comm-SWAP12-BOX⟨4·30⟩ : _
lem-comm-SWAP12-BOX⟨4·30⟩ = R004.lem-comm-SWAP12-BOX⟨4·30⟩
lem-cQ-at03203442 : _
lem-cQ-at03203442 = D003.lem-cQ-at03203442
sD005 : SD005
sD005 = (λ c → lem-comm-CX02-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-CX04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CX12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX14-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CX21-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX24-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-CX31-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX32-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX42-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-SWAP13-BOX⟨0·42⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP14-BOX⟨0·23⟩ (lit c)) ∷ᵃ (λ c → lem-comm-CX03-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CX30-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CX40-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CX41-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-SWAP12-BOX⟨3·04⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP12-BOX⟨3·40⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP14-BOX⟨2·03⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP23-BOX⟨0·41⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP24-BOX⟨0·13⟩ (lit c)) ∷ᵃ (λ c → lem-comm-CX20-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-SWAP02-BOX⟨3·41⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP03-BOX⟨4·21⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP04-BOX⟨3·21⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP12-BOX⟨4·03⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP13-BOX⟨2·04⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP14-BOX⟨3·02⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP12-BOX⟨4·30⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP13-BOX⟨4·20⟩ (lit c)) ∷ᵃ lem-cQ-at021021 ∷ᵃ lem-sym-ab-at0210243143 ∷ᵃ lem-sym-ab-at032032 ∷ᵃ lem-sym-ab-at1221 ∷ᵃ lem-cQ-at0213243041 ∷ᵃ lem-cQ-at0214233041 ∷ᵃ lem-cQ-at0310213442 ∷ᵃ lem-sym-ab-at021021 ∷ᵃ lem-sym-ab-at0220 ∷ᵃ lem-cQ-at03203442 ∷ᵃ nil
lem-nat-SWbc-at12213443 : _
lem-nat-SWbc-at12213443 = D005.lem-nat-SWbc-at12213443 sD005
lem-nat-SWbc-at14233241 : _
lem-nat-SWbc-at14233241 = D005.lem-nat-SWbc-at14233241 sD005
lem-cQ-at03143140 : _
lem-cQ-at03143140 = D005.lem-cQ-at03143140 sD005
lem-nat-SWbc-at03143140 : _
lem-nat-SWbc-at03143140 = D005.lem-nat-SWbc-at03143140 sD005
lem-cQ-at0314213240 : _
lem-cQ-at0314213240 = D005.lem-cQ-at0314213240 sD005
lem-cQ-at03243240 : _
lem-cQ-at03243240 = D005.lem-cQ-at03243240 sD005
lem-nat-SWbc-at0314213240 : _
lem-nat-SWbc-at0314213240 = D005.lem-nat-SWbc-at0314213240 sD005
lem-cQ-at03103441 : _
lem-cQ-at03103441 = D005.lem-cQ-at03103441 sD005
lem-cQ-at0310243241 : _
lem-cQ-at0310243241 = D005.lem-cQ-at0310243241 sD005
lem-nat-SWbc-at0310243142 : _
lem-nat-SWbc-at0310243142 = D005.lem-nat-SWbc-at0310243142 sD005
lem-box-tQ-at0310213442 : _
lem-box-tQ-at0310213442 = D005.lem-box-tQ-at0310213442 sD005
lem-nat-SWbc-at0310213442 : _
lem-nat-SWbc-at0310213442 = D005.lem-nat-SWbc-at0310213442 sD005
lem-cQ-at0312203441 : _
lem-cQ-at0312203441 = D005.lem-cQ-at0312203441 sD005
lem-nat-SWbc-at0312203441 : _
lem-nat-SWbc-at0312203441 = D005.lem-nat-SWbc-at0312203441 sD005
lem-cQ-at0312243041 : _
lem-cQ-at0312243041 = D005.lem-cQ-at0312243041 sD005
lem-nat-SWbc-at0312243041 : _
lem-nat-SWbc-at0312243041 = D005.lem-nat-SWbc-at0312243041 sD005
lem-nat-SWbc-at3443 : _
lem-nat-SWbc-at3443 = D005.lem-nat-SWbc-at3443 sD005
lem-cQ-at03122031 : _
lem-cQ-at03122031 = D005.lem-cQ-at03122031 sD005
lem-cQ-at031031 : _
lem-cQ-at031031 = D005.lem-cQ-at031031 sD005
lem-nat-SWbc-at031031 : _
lem-nat-SWbc-at031031 = D005.lem-nat-SWbc-at031031 sD005
lem-cQ-at03143041 : _
lem-cQ-at03143041 = D005.lem-cQ-at03143041 sD005
lem-nat-SWbc-at03143041 : _
lem-nat-SWbc-at03143041 = D005.lem-nat-SWbc-at03143041 sD005
lem-cQ-at0314203241 : _
lem-cQ-at0314203241 = D005.lem-cQ-at0314203241 sD005
lem-cQ-at02142041 : _
lem-cQ-at02142041 = D005.lem-cQ-at02142041 sD005
lem-tP-at0214233041 : _
lem-tP-at0214233041 = D005.lem-tP-at0214233041 sD005
lem-nat-SWbc-at0314203241 : _
lem-nat-SWbc-at0314203241 = D005.lem-nat-SWbc-at0314203241 sD005
lem-box-tQ-at0214233041 : _
lem-box-tQ-at0214233041 = D005.lem-box-tQ-at0214233041 sD005
lem-nat-SWbc-at0210213443 : _
lem-nat-SWbc-at0210213443 = D005.lem-nat-SWbc-at0210213443 sD005
lem-cQ-at02132130 : _
lem-cQ-at02132130 = D005.lem-cQ-at02132130 sD005
lem-cQ-at02132031 : _
lem-cQ-at02132031 = D005.lem-cQ-at02132031 sD005
lem-tP-at0310213442 : _
lem-tP-at0310213442 = D005.lem-tP-at0310213442 sD005
lem-tP-at0213243041 : _
lem-tP-at0213243041 = D005.lem-tP-at0213243041 sD005
lem-box-tQ-at0213243041 : _
lem-box-tQ-at0213243041 = D005.lem-box-tQ-at0213243041 sD005
lem-box-tQ-at021021 : _
lem-box-tQ-at021021 = D005.lem-box-tQ-at021021 sD005
lem-cQ-at03122130 : _
lem-cQ-at03122130 = D005.lem-cQ-at03122130 sD005
lem-nat-SWbc-at021021 : _
lem-nat-SWbc-at021021 = D005.lem-nat-SWbc-at021021 sD005
lem-cQ-at02102331 : _
lem-cQ-at02102331 = D005.lem-cQ-at02102331 sD005
lem-cQ-at03243042 : _
lem-cQ-at03243042 = D005.lem-cQ-at03243042 sD005
lem-cQ-at142142 : _
lem-cQ-at142142 = D005.lem-cQ-at142142 sD005
lem-box-perm-2134-at0210243143 : _
lem-box-perm-2134-at0210243143 = D005.lem-box-perm-2134-at0210243143 sD005
lem-cQ-at04122041 : _
lem-cQ-at04122041 = D005.lem-cQ-at04122041 sD005
lem-cQ-at0412233041 : _
lem-cQ-at0412233041 = D005.lem-cQ-at0412233041 sD005
lem-nat-SWbc-at0410213243 : _
lem-nat-SWbc-at0410213243 = D005.lem-nat-SWbc-at0410213243 sD005
lem-cQ-at04103143 : _
lem-cQ-at04103143 = D005.lem-cQ-at04103143 sD005
lem-cQ-at04233042 : _
lem-cQ-at04233042 = D005.lem-cQ-at04233042 sD005
lem-cQ-at041041 : _
lem-cQ-at041041 = D005.lem-cQ-at041041 sD005
lem-cQ-at0410233241 : _
lem-cQ-at0410233241 = D005.lem-cQ-at0410233241 sD005
lem-cQ-at0412213043 : _
lem-cQ-at0412213043 = D005.lem-cQ-at0412213043 sD005
lem-cQ-at0413213240 : _
lem-cQ-at0413213240 = D005.lem-cQ-at0413213240 sD005
lem-cQ-at04233240 : _
lem-cQ-at04233240 = D005.lem-cQ-at04233240 sD005
lem-cQ-at0440 : _
lem-cQ-at0440 = D005.lem-cQ-at0440 sD005
lem-cQ-at0413203142 : _
lem-cQ-at0413203142 = D005.lem-cQ-at0413203142 sD005
lem-cQ-at02142140 : _
lem-cQ-at02142140 = D005.lem-cQ-at02142140 sD005
lem-cQ-at0413213042 : _
lem-cQ-at0413213042 = D005.lem-cQ-at0413213042 sD005
lem-cQ-at0412233140 : _
lem-cQ-at0412233140 = D005.lem-cQ-at0412233140 sD005
lem-cQ-at0410233142 : _
lem-cQ-at0410233142 = D005.lem-cQ-at0410233142 sD005
lem-cQ-at04122140 : _
lem-cQ-at04122140 = D005.lem-cQ-at04122140 sD005
lem-cQ-at0413203241 : _
lem-cQ-at0413203241 = D005.lem-cQ-at0413203241 sD005
lem-cQ-at04133140 : _
lem-cQ-at04133140 = D005.lem-cQ-at04133140 sD005
sD007 : SD007
sD007 = (λ c → lem-comm-CS12-TOFF034 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-TOFF034 (lit c)) ∷ᵃ (λ c → lem-comm-CZ04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CZ12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CZ13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CZ14-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CZ24-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF301-CSd24 (lit c)) ∷ᵃ (λ c → lem-comm-CS23-TOFF401 (lit c)) ∷ᵃ (λ c → lem-comm-CS24-TOFF301 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-TOFF401 (lit c)) ∷ᵃ (λ c → lem-comm-CSd24-TOFF301 (lit c)) ∷ᵃ (λ c → lem-comm-CZ03-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CZ24-TOFF301 (lit c)) ∷ᵃ (λ c → lem-comm-CZ02-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-SWAP03-BOX⟨2·14⟩ (lit c)) ∷ᵃ (λ c → lem-comm-SWAP03-BOX⟨2·41⟩ (lit c)) ∷ᵃ lem-box-perm-2134-at03102132 ∷ᵃ lem-box-tQ-at0210213443 ∷ᵃ lem-box-tQ-at0213243140 ∷ᵃ lem-box-tQ-at0220 ∷ᵃ lem-box-tQ-at03102132 ∷ᵃ lem-box-tQ-at0410213243 ∷ᵃ lem-box-tQ-at14233241 ∷ᵃ lem-cQ-at02102441 ∷ᵃ lem-cQ-at0213213440 ∷ᵃ lem-cQ-at0214203143 ∷ᵃ lem-cQ-at022330 ∷ᵃ lem-cQ-at02233440 ∷ᵃ lem-cQ-at022440 ∷ᵃ lem-cQ-at033440 ∷ᵃ lem-cQ-at12243143 ∷ᵃ lem-cQ-at14213243 ∷ᵃ lem-cQ-at1441 ∷ᵃ lem-cQ-at2442 ∷ᵃ lem-tP-at021021 ∷ᵃ lem-tP-at0210213443 ∷ᵃ lem-tP-at0213243140 ∷ᵃ lem-tP-at03102132 ∷ᵃ lem-tP-at032032 ∷ᵃ lem-box-perm-2134-at0210243143 ∷ᵃ lem-box-tQ-at021021 ∷ᵃ lem-box-tQ-at0213243041 ∷ᵃ lem-box-tQ-at0214233041 ∷ᵃ lem-box-tQ-at0310213442 ∷ᵃ lem-cQ-at02102331 ∷ᵃ lem-cQ-at02132031 ∷ᵃ lem-cQ-at02132130 ∷ᵃ lem-cQ-at02142041 ∷ᵃ lem-cQ-at0310243241 ∷ᵃ lem-cQ-at031031 ∷ᵃ lem-cQ-at03103441 ∷ᵃ lem-cQ-at03122031 ∷ᵃ lem-cQ-at0312203441 ∷ᵃ lem-cQ-at03122130 ∷ᵃ lem-cQ-at0312243041 ∷ᵃ lem-cQ-at0314203241 ∷ᵃ lem-cQ-at0314213240 ∷ᵃ lem-cQ-at03143041 ∷ᵃ lem-cQ-at03143140 ∷ᵃ lem-cQ-at03243042 ∷ᵃ lem-cQ-at03243240 ∷ᵃ lem-cQ-at04103143 ∷ᵃ lem-cQ-at04122041 ∷ᵃ lem-cQ-at0412233041 ∷ᵃ lem-cQ-at04233042 ∷ᵃ lem-cQ-at142142 ∷ᵃ lem-tP-at0213243041 ∷ᵃ lem-tP-at0214233041 ∷ᵃ lem-tP-at0310213442 ∷ᵃ nil
lem-box-tQ-at02233440 : _
lem-box-tQ-at02233440 = D007.lem-box-tQ-at02233440 sD007
lem-box-tQ-at0213213440 : _
lem-box-tQ-at0213213440 = D007.lem-box-tQ-at0213213440 sD007
lem-P-box-at0213243140 : _
lem-P-box-at0213243140 = D007.lem-P-box-at0213243140 sD007
lem-VPQ-at0213243140 : _
lem-VPQ-at0213243140 = D007.lem-VPQ-at0213243140 sD007
lem-CXbc-box-at0220 : _
lem-CXbc-box-at0220 = D007.lem-CXbc-box-at0220 sD007
lem-CXcb-box-at0220 : _
lem-CXcb-box-at0220 = D007.lem-CXcb-box-at0220 sD007
lem-nat-SWbc-at0220 : _
lem-nat-SWbc-at0220 = D007.lem-nat-SWbc-at0220 sD007
lem-tP-at022330 : _
lem-tP-at022330 = D007.lem-tP-at022330 sD007
lem-tP-at14213243 : _
lem-tP-at14213243 = D007.lem-tP-at14213243 sD007
lem-CXbc-box-at03102132 : _
lem-CXbc-box-at03102132 = D007.lem-CXbc-box-at03102132 sD007
lem-CXcb-box-at03102132 : _
lem-CXcb-box-at03102132 = D007.lem-CXcb-box-at03102132 sD007
lem-tP-at0214203143 : _
lem-tP-at0214203143 = D007.lem-tP-at0214203143 sD007
lem-tP-at022440 : _
lem-tP-at022440 = D007.lem-tP-at022440 sD007
lem-box-tQ-at022440 : _
lem-box-tQ-at022440 = D007.lem-box-tQ-at022440 sD007
lem-tP-at02233440 : _
lem-tP-at02233440 = D007.lem-tP-at02233440 sD007
lem-tP-at1441 : _
lem-tP-at1441 = D007.lem-tP-at1441 sD007
lem-tP-at02102441 : _
lem-tP-at02102441 = D007.lem-tP-at02102441 sD007
lem-box-tQ-at02102441 : _
lem-box-tQ-at02102441 = D007.lem-box-tQ-at02102441 sD007
lem-tP-at2442 : _
lem-tP-at2442 = D007.lem-tP-at2442 sD007
lem-tP-at12243143 : _
lem-tP-at12243143 = D007.lem-tP-at12243143 sD007
lem-CXbc-box-at14233241 : _
lem-CXbc-box-at14233241 = D007.lem-CXbc-box-at14233241 sD007
lem-CXcb-box-at14233241 : _
lem-CXcb-box-at14233241 = D007.lem-CXcb-box-at14233241 sD007
lem-box-tQ-at03143140 : _
lem-box-tQ-at03143140 = D007.lem-box-tQ-at03143140 sD007
lem-tP-at0314213240 : _
lem-tP-at0314213240 = D007.lem-tP-at0314213240 sD007
lem-box-tQ-at03243240 : _
lem-box-tQ-at03243240 = D007.lem-box-tQ-at03243240 sD007
lem-box-tQ-at0314213240 : _
lem-box-tQ-at0314213240 = D007.lem-box-tQ-at0314213240 sD007
lem-tP-at03143140 : _
lem-tP-at03143140 = D007.lem-tP-at03143140 sD007
lem-tP-at03243240 : _
lem-tP-at03243240 = D007.lem-tP-at03243240 sD007
lem-tP-at033440 : _
lem-tP-at033440 = D007.lem-tP-at033440 sD007
lem-box-tQ-at03103441 : _
lem-box-tQ-at03103441 = D007.lem-box-tQ-at03103441 sD007
lem-tP-at0310243241 : _
lem-tP-at0310243241 = D007.lem-tP-at0310243241 sD007
lem-box-tQ-at0310243241 : _
lem-box-tQ-at0310243241 = D007.lem-box-tQ-at0310243241 sD007
lem-tP-at03103441 : _
lem-tP-at03103441 = D007.lem-tP-at03103441 sD007
lem-CXbc-box-at0310213442 : _
lem-CXbc-box-at0310213442 = D007.lem-CXbc-box-at0310213442 sD007
lem-CXcb-box-at0310213442 : _
lem-CXcb-box-at0310213442 = D007.lem-CXcb-box-at0310213442 sD007
lem-box-tQ-at0312203441 : _
lem-box-tQ-at0312203441 = D007.lem-box-tQ-at0312203441 sD007
lem-tP-at0312243041 : _
lem-tP-at0312243041 = D007.lem-tP-at0312243041 sD007
lem-box-tQ-at0312243041 : _
lem-box-tQ-at0312243041 = D007.lem-box-tQ-at0312243041 sD007
lem-tP-at0312203441 : _
lem-tP-at0312203441 = D007.lem-tP-at0312203441 sD007
lem-box-tQ-at03122031 : _
lem-box-tQ-at03122031 = D007.lem-box-tQ-at03122031 sD007
lem-box-tQ-at031031 : _
lem-box-tQ-at031031 = D007.lem-box-tQ-at031031 sD007
lem-tP-at031031 : _
lem-tP-at031031 = D007.lem-tP-at031031 sD007
lem-P-box-at03102132 : _
lem-P-box-at03102132 = D007.lem-P-box-at03102132 sD007
lem-box-tQ-at03143041 : _
lem-box-tQ-at03143041 = D007.lem-box-tQ-at03143041 sD007
lem-box-tQ-at0314203241 : _
lem-box-tQ-at0314203241 = D007.lem-box-tQ-at0314203241 sD007
lem-box-tQ-at02142041 : _
lem-box-tQ-at02142041 = D007.lem-box-tQ-at02142041 sD007
lem-nat-SWbc-at02142041 : _
lem-nat-SWbc-at02142041 = D007.lem-nat-SWbc-at02142041 sD007
lem-VPQ-at0214233041 : _
lem-VPQ-at0214233041 = D007.lem-VPQ-at0214233041 sD007
lem-P-box-at0214233041 : _
lem-P-box-at0214233041 = D007.lem-P-box-at0214233041 sD007
lem-CXbc-box-at0210213443 : _
lem-CXbc-box-at0210213443 = D007.lem-CXbc-box-at0210213443 sD007
lem-CXcb-box-at0210213443 : _
lem-CXcb-box-at0210213443 = D007.lem-CXcb-box-at0210213443 sD007
lem-P-box-at0210213443 : _
lem-P-box-at0210213443 = D007.lem-P-box-at0210213443 sD007
lem-CXbc-box-at0214233041 : _
lem-CXbc-box-at0214233041 = D007.lem-CXbc-box-at0214233041 sD007
lem-CXcb-box-at0214233041 : _
lem-CXcb-box-at0214233041 = D007.lem-CXcb-box-at0214233041 sD007
lem-nat-SWbc-at0214233041 : _
lem-nat-SWbc-at0214233041 = D007.lem-nat-SWbc-at0214233041 sD007
lem-box-tQ-at02132130 : _
lem-box-tQ-at02132130 = D007.lem-box-tQ-at02132130 sD007
lem-tP-at03143041 : _
lem-tP-at03143041 = D007.lem-tP-at03143041 sD007
lem-tP-at02132031 : _
lem-tP-at02132031 = D007.lem-tP-at02132031 sD007
lem-P-box-at0310213442 : _
lem-P-box-at0310213442 = D007.lem-P-box-at0310213442 sD007
lem-VPQ-at0310213442 : _
lem-VPQ-at0310213442 = D007.lem-VPQ-at0310213442 sD007
lem-box-tQ-at02132031 : _
lem-box-tQ-at02132031 = D007.lem-box-tQ-at02132031 sD007
lem-tP-at02132130 : _
lem-tP-at02132130 = D007.lem-tP-at02132130 sD007
lem-VPQ-at0213243041 : _
lem-VPQ-at0213243041 = D007.lem-VPQ-at0213243041 sD007
lem-P-box-at0213243041 : _
lem-P-box-at0213243041 = D007.lem-P-box-at0213243041 sD007
lem-box-tQ-at03122130 : _
lem-box-tQ-at03122130 = D007.lem-box-tQ-at03122130 sD007
lem-P-box-at021021 : _
lem-P-box-at021021 = D007.lem-P-box-at021021 sD007
lem-tP-at03122031 : _
lem-tP-at03122031 = D007.lem-tP-at03122031 sD007
lem-tP-at03122130 : _
lem-tP-at03122130 = D007.lem-tP-at03122130 sD007
lem-tP-at02142041 : _
lem-tP-at02142041 = D007.lem-tP-at02142041 sD007
lem-tP-at0314203241 : _
lem-tP-at0314203241 = D007.lem-tP-at0314203241 sD007
lem-CXbc-box-at021021 : _
lem-CXbc-box-at021021 = D007.lem-CXbc-box-at021021 sD007
lem-CXcb-box-at021021 : _
lem-CXcb-box-at021021 = D007.lem-CXcb-box-at021021 sD007
lem-tP-at02102331 : _
lem-tP-at02102331 = D007.lem-tP-at02102331 sD007
lem-box-tQ-at03243042 : _
lem-box-tQ-at03243042 = D007.lem-box-tQ-at03243042 sD007
lem-box-tQ-at142142 : _
lem-box-tQ-at142142 = D007.lem-box-tQ-at142142 sD007
lem-tP-at03243042 : _
lem-tP-at03243042 = D007.lem-tP-at03243042 sD007
lem-box-tQ-at02102331 : _
lem-box-tQ-at02102331 = D007.lem-box-tQ-at02102331 sD007
lem-tP-at142142 : _
lem-tP-at142142 = D007.lem-tP-at142142 sD007
lem-box-tQ-at04122041 : _
lem-box-tQ-at04122041 = D007.lem-box-tQ-at04122041 sD007
lem-tP-at0412233041 : _
lem-tP-at0412233041 = D007.lem-tP-at0412233041 sD007
lem-tP-at04122041 : _
lem-tP-at04122041 = D007.lem-tP-at04122041 sD007
lem-CXbc-box-at0410213243 : _
lem-CXbc-box-at0410213243 = D007.lem-CXbc-box-at0410213243 sD007
lem-CXcb-box-at0410213243 : _
lem-CXcb-box-at0410213243 = D007.lem-CXcb-box-at0410213243 sD007
lem-box-tQ-at04103143 : _
lem-box-tQ-at04103143 = D007.lem-box-tQ-at04103143 sD007
lem-tP-at04103143 : _
lem-tP-at04103143 = D007.lem-tP-at04103143 sD007
lem-tP-at04233042 : _
lem-tP-at04233042 = D007.lem-tP-at04233042 sD007
sD009 : SD009
sD009 = (λ c → lem-comm-CS03-TOFF412 (lit c)) ∷ᵃ (λ c → lem-comm-CS12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CS13-TOFF024 (lit c)) ∷ᵃ (λ c → lem-comm-CS14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CS24-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-CS24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-CSd02-TOFF134 (lit c)) ∷ᵃ (λ c → lem-comm-CSd03-TOFF412 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-TOFF034 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-TOFF403 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-TOFF024 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-TOFF014 (lit c)) ∷ᵃ (λ c → lem-comm-CSd24-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-CSd24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-CX12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX21-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX24-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-CX31-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX32-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CZ04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CZ04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CZ12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CZ12-TOFF034 (lit c)) ∷ᵃ (λ c → lem-comm-CZ14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CZ24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF013-CSd24 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF014-CSd23 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF024-CSd13 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF204-CSd13 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF312-CSd04 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF412-CSd03 (lit c)) ∷ᵃ (λ c → lem-comm-CS04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CS04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CS13-TOFF204 (lit c)) ∷ᵃ (λ c → lem-comm-CS14-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-TOFF304 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-TOFF204 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CX40-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CZ03-TOFF214 (lit c)) ∷ᵃ (λ c → lem-comm-CZ12-TOFF304 (lit c)) ∷ᵃ (λ c → lem-comm-CZ12-TOFF403 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF304-CSd12 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF023-CSd14 (lit c)) ∷ᵃ lem-CXbc-box-at032032 ∷ᵃ lem-CXbc-box-at04203243 ∷ᵃ lem-CXbc-box-at13243142 ∷ᵃ lem-CXbc-box-at13243241 ∷ᵃ lem-CXbc-box-at14233142 ∷ᵃ lem-CXcb-box-at032032 ∷ᵃ lem-CXcb-box-at04203243 ∷ᵃ lem-CXcb-box-at13243142 ∷ᵃ lem-CXcb-box-at13243241 ∷ᵃ lem-CXcb-box-at14233142 ∷ᵃ lem-VPQ-at021021 ∷ᵃ lem-VPQ-at03102132 ∷ᵃ lem-VPQ-at0410213243 ∷ᵃ lem-VPQ-at04203243 ∷ᵃ lem-VPQ-at13243142 ∷ᵃ lem-VPQ-at13243241 ∷ᵃ lem-VPQ-at14233142 ∷ᵃ lem-box-tQ ∷ᵃ lem-box-tQ-at0210243143 ∷ᵃ lem-box-tQ-at0214203143 ∷ᵃ lem-box-tQ-at0214213043 ∷ᵃ lem-box-tQ-at0310243142 ∷ᵃ lem-box-tQ-at0330 ∷ᵃ lem-box-tQ-at043043 ∷ᵃ lem-box-tQ-at1221 ∷ᵃ lem-box-tQ-at122331 ∷ᵃ lem-box-tQ-at12243143 ∷ᵃ lem-box-tQ-at122441 ∷ᵃ lem-box-tQ-at132132 ∷ᵃ lem-box-tQ-at13213442 ∷ᵃ lem-box-tQ-at1331 ∷ᵃ lem-box-tQ-at133441 ∷ᵃ lem-box-tQ-at2332 ∷ᵃ lem-box-tQ-at243243 ∷ᵃ lem-box-tQ-at3443 ∷ᵃ lem-tP ∷ᵃ lem-tP-at0110 ∷ᵃ lem-tP-at0210243143 ∷ᵃ lem-tP-at0214213043 ∷ᵃ lem-tP-at0310243142 ∷ᵃ lem-tP-at0314203142 ∷ᵃ lem-tP-at0330 ∷ᵃ lem-tP-at043043 ∷ᵃ lem-tP-at1221 ∷ᵃ lem-tP-at122331 ∷ᵃ lem-tP-at122441 ∷ᵃ lem-tP-at132132 ∷ᵃ lem-tP-at13213442 ∷ᵃ lem-tP-at1331 ∷ᵃ lem-tP-at2332 ∷ᵃ lem-tP-at243243 ∷ᵃ lem-tP-at3443 ∷ᵃ nil
lem-VPQ : _
lem-VPQ = D009.lem-VPQ sD009
lem-t-cP : _
lem-t-cP = D009.lem-t-cP sD009
lem-VPQ-at0210243143 : _
lem-VPQ-at0210243143 = D009.lem-VPQ-at0210243143 sD009
lem-t-cP-at0210243143 : _
lem-t-cP-at0210243143 = D009.lem-t-cP-at0210243143 sD009
lem-VPQ-at243243 : _
lem-VPQ-at243243 = D009.lem-VPQ-at243243 sD009
lem-t-cP-at243243 : _
lem-t-cP-at243243 = D009.lem-t-cP-at243243 sD009
lem-VPQ-at122441 : _
lem-VPQ-at122441 = D009.lem-VPQ-at122441 sD009
lem-t-cP-at122441 : _
lem-t-cP-at122441 = D009.lem-t-cP-at122441 sD009
lem-CXcb-box : _
lem-CXcb-box = D009.lem-CXcb-box sD009
lem-CXbc-box : _
lem-CXbc-box = D009.lem-CXbc-box sD009
lem-P-box : _
lem-P-box = D009.lem-P-box sD009
lem-CXbc-box-at1221 : _
lem-CXbc-box-at1221 = D009.lem-CXbc-box-at1221 sD009
lem-CXcb-box-at1221 : _
lem-CXcb-box-at1221 = D009.lem-CXcb-box-at1221 sD009
lem-P-box-at1221 : _
lem-P-box-at1221 = D009.lem-P-box-at1221 sD009
lem-VPQ-at1221 : _
lem-VPQ-at1221 = D009.lem-VPQ-at1221 sD009
lem-P-box-at2332 : _
lem-P-box-at2332 = D009.lem-P-box-at2332 sD009
lem-VPQ-at2332 : _
lem-VPQ-at2332 = D009.lem-VPQ-at2332 sD009
lem-SWbc-box-at13243142 : _
lem-SWbc-box-at13243142 = D009.lem-SWbc-box-at13243142 sD009
lem-P-box-at122331 : _
lem-P-box-at122331 = D009.lem-P-box-at122331 sD009
lem-VPQ-at122331 : _
lem-VPQ-at122331 = D009.lem-VPQ-at122331 sD009
lem-SWbc-box-at13243241 : _
lem-SWbc-box-at13243241 = D009.lem-SWbc-box-at13243241 sD009
lem-P-box-at132132 : _
lem-P-box-at132132 = D009.lem-P-box-at132132 sD009
lem-VPQ-at132132 : _
lem-VPQ-at132132 = D009.lem-VPQ-at132132 sD009
lem-CXbc-box-at12243143 : _
lem-CXbc-box-at12243143 = D009.lem-CXbc-box-at12243143 sD009
lem-CXcb-box-at12243143 : _
lem-CXcb-box-at12243143 = D009.lem-CXcb-box-at12243143 sD009
lem-SWbc-box-at14233142 : _
lem-SWbc-box-at14233142 = D009.lem-SWbc-box-at14233142 sD009
lem-QVQ-at14233142 : _
lem-QVQ-at14233142 = D009.lem-QVQ-at14233142 sD009
lem-P-box-at13213442 : _
lem-P-box-at13213442 = D009.lem-P-box-at13213442 sD009
lem-VPQ-at13213442 : _
lem-VPQ-at13213442 = D009.lem-VPQ-at13213442 sD009
lem-P-box-at1331 : _
lem-P-box-at1331 = D009.lem-P-box-at1331 sD009
lem-VPQ-at1331 : _
lem-VPQ-at1331 = D009.lem-VPQ-at1331 sD009
lem-Su-box : _
lem-Su-box = D009.lem-Su-box sD009
lem-Sdu-box : _
lem-Sdu-box = D009.lem-Sdu-box sD009
lem-CSu-box-1 : _
lem-CSu-box-1 = D009.lem-CSu-box-1 sD009
lem-CSdu-box-1 : _
lem-CSdu-box-1 = D009.lem-CSdu-box-1 sD009
lem-CSu-box-2 : _
lem-CSu-box-2 = D009.lem-CSu-box-2 sD009
lem-CSdu-box-2 : _
lem-CSdu-box-2 = D009.lem-CSdu-box-2 sD009
lem-VPQ-at0110 : _
lem-VPQ-at0110 = D009.lem-VPQ-at0110 sD009
lem-CXbc-box-at133441 : _
lem-CXbc-box-at133441 = D009.lem-CXbc-box-at133441 sD009
lem-CXcb-box-at133441 : _
lem-CXcb-box-at133441 = D009.lem-CXcb-box-at133441 sD009
lem-QVQ-at13243241 : _
lem-QVQ-at13243241 = D009.lem-QVQ-at13243241 sD009
lem-QVQ-at021021 : _
lem-QVQ-at021021 = D009.lem-QVQ-at021021 sD009
lem-CXbc-box-at13213442 : _
lem-CXbc-box-at13213442 = D009.lem-CXbc-box-at13213442 sD009
lem-CXcb-box-at13213442 : _
lem-CXcb-box-at13213442 = D009.lem-CXcb-box-at13213442 sD009
lem-QVQ-at13243142 : _
lem-QVQ-at13243142 = D009.lem-QVQ-at13243142 sD009
lem-QVQ-at03102132 : _
lem-QVQ-at03102132 = D009.lem-QVQ-at03102132 sD009
lem-P-box-at3443 : _
lem-P-box-at3443 = D009.lem-P-box-at3443 sD009
lem-VPQ-at3443 : _
lem-VPQ-at3443 = D009.lem-VPQ-at3443 sD009
lem-QVQ-at0410213243 : _
lem-QVQ-at0410213243 = D009.lem-QVQ-at0410213243 sD009
lem-VPQ-at043043 : _
lem-VPQ-at043043 = D009.lem-VPQ-at043043 sD009
lem-CXbc-box-at043043 : _
lem-CXbc-box-at043043 = D009.lem-CXbc-box-at043043 sD009
lem-CXcb-box-at043043 : _
lem-CXcb-box-at043043 = D009.lem-CXcb-box-at043043 sD009
lem-QVQ-at04203243 : _
lem-QVQ-at04203243 = D009.lem-QVQ-at04203243 sD009
lem-P-box-at0330 : _
lem-P-box-at0330 = D009.lem-P-box-at0330 sD009
lem-VPQ-at0330 : _
lem-VPQ-at0330 = D009.lem-VPQ-at0330 sD009
lem-VPQ-at0314203142 : _
lem-VPQ-at0314203142 = D009.lem-VPQ-at0314203142 sD009
lem-P-box-at0310243142 : _
lem-P-box-at0310243142 = D009.lem-P-box-at0310243142 sD009
lem-VPQ-at0310243142 : _
lem-VPQ-at0310243142 = D009.lem-VPQ-at0310243142 sD009
lem-SWbc-box-at04203243 : _
lem-SWbc-box-at04203243 = D009.lem-SWbc-box-at04203243 sD009
lem-SWbc-box-at032032 : _
lem-SWbc-box-at032032 = D009.lem-SWbc-box-at032032 sD009
lem-t-cP-at043043 : _
lem-t-cP-at043043 = D009.lem-t-cP-at043043 sD009
lem-CXbc-box-at0330 : _
lem-CXbc-box-at0330 = D009.lem-CXbc-box-at0330 sD009
lem-CXcb-box-at0330 : _
lem-CXcb-box-at0330 = D009.lem-CXcb-box-at0330 sD009
lem-CSdu-box-2-at243243 : _
lem-CSdu-box-2-at243243 = D009.lem-CSdu-box-2-at243243 sD009
lem-Su-box-at243243 : _
lem-Su-box-at243243 = D009.lem-Su-box-at243243 sD009
lem-CSdu-box-2-at122441 : _
lem-CSdu-box-2-at122441 = D009.lem-CSdu-box-2-at122441 sD009
lem-Su-box-at122441 : _
lem-Su-box-at122441 = D009.lem-Su-box-at122441 sD009
lem-CSdu-box-2-at0210243143 : _
lem-CSdu-box-2-at0210243143 = D009.lem-CSdu-box-2-at0210243143 sD009
lem-Su-box-at0210243143 : _
lem-Su-box-at0210243143 = D009.lem-Su-box-at0210243143 sD009
lem-CSu-box-2-at243243 : _
lem-CSu-box-2-at243243 = D009.lem-CSu-box-2-at243243 sD009
lem-CSu-box-2-at122441 : _
lem-CSu-box-2-at122441 = D009.lem-CSu-box-2-at122441 sD009
lem-CXbc-box-at0214203143 : _
lem-CXbc-box-at0214203143 = D009.lem-CXbc-box-at0214203143 sD009
lem-CXcb-box-at0214203143 : _
lem-CXcb-box-at0214203143 = D009.lem-CXcb-box-at0214203143 sD009
lem-P-box-at0214213043 : _
lem-P-box-at0214213043 = D009.lem-P-box-at0214213043 sD009
sD010 : SD010
sD010 = (λ c → lem-comm-CS13-TOFF024 (lit c)) ∷ᵃ (λ c → lem-comm-CS14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CS24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-TOFF034 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-TOFF024 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-TOFF014 (lit c)) ∷ᵃ (λ c → lem-comm-CSd24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-CX04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CX13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX14-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CX21-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX24-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-CX31-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX32-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX42-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-CZ04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CZ14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF013-CSd24 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF014-CSd23 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF024-CSd13 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF204-CSd13 (lit c)) ∷ᵃ (λ c → lem-comm-CS02-TOFF314 (lit c)) ∷ᵃ (λ c → lem-comm-CS03-TOFF214 (lit c)) ∷ᵃ (λ c → lem-comm-CS04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CS04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CS04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CS12-TOFF304 (lit c)) ∷ᵃ (λ c → lem-comm-CS13-TOFF204 (lit c)) ∷ᵃ (λ c → lem-comm-CS23-TOFF014 (lit c)) ∷ᵃ (λ c → lem-comm-CSd02-TOFF314 (lit c)) ∷ᵃ (λ c → lem-comm-CSd03-TOFF214 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-TOFF304 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-TOFF204 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-TOFF203 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-TOFF302 (lit c)) ∷ᵃ (λ c → lem-comm-CSd24-TOFF301 (lit c)) ∷ᵃ (λ c → lem-comm-CX40-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CX41-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CZ13-TOFF024 (lit c)) ∷ᵃ (λ c → lem-comm-CZ13-TOFF204 (lit c)) ∷ᵃ (λ c → lem-comm-CZ14-TOFF203 (lit c)) ∷ᵃ (λ c → lem-comm-CZ14-TOFF302 (lit c)) ∷ᵃ (λ c → lem-comm-CZ23-TOFF014 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF213-CSd04 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF214-CSd03 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF314-CSd02 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF023-CSd14 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF203-CSd14 (lit c)) ∷ᵃ lem-CXbc-box-at0213243140 ∷ᵃ lem-CXcb-box-at0213243140 ∷ᵃ lem-VPQ-at0210213443 ∷ᵃ lem-VPQ-at0220 ∷ᵃ lem-VPQ-at032032 ∷ᵃ lem-VPQ-at14233241 ∷ᵃ lem-box-tQ-at0210233441 ∷ᵃ lem-box-tQ-at0210243143 ∷ᵃ lem-box-tQ-at0214203143 ∷ᵃ lem-box-tQ-at0214213043 ∷ᵃ lem-box-tQ-at022330 ∷ᵃ lem-box-tQ-at0312213440 ∷ᵃ lem-box-tQ-at0312243140 ∷ᵃ lem-box-tQ-at0314203142 ∷ᵃ lem-box-tQ-at0314213042 ∷ᵃ lem-box-tQ-at122331 ∷ᵃ lem-box-tQ-at12233441 ∷ᵃ lem-box-tQ-at122441 ∷ᵃ lem-box-tQ-at132132 ∷ᵃ lem-box-tQ-at1331 ∷ᵃ lem-box-tQ-at14213243 ∷ᵃ lem-box-tQ-at143143 ∷ᵃ lem-box-tQ-at1441 ∷ᵃ lem-box-tQ-at2332 ∷ᵃ lem-box-tQ-at243243 ∷ᵃ lem-tP-at0210233441 ∷ᵃ lem-tP-at0210243143 ∷ᵃ lem-tP-at0213203441 ∷ᵃ lem-tP-at0214213043 ∷ᵃ lem-tP-at0312243140 ∷ᵃ lem-tP-at0314213042 ∷ᵃ lem-tP-at12213443 ∷ᵃ lem-tP-at12233441 ∷ᵃ lem-tP-at122441 ∷ᵃ lem-tP-at143143 ∷ᵃ lem-tP-at233442 ∷ᵃ lem-tP-at243243 ∷ᵃ lem-CXbc-box-at0220 ∷ᵃ lem-CXbc-box-at03102132 ∷ᵃ lem-CXcb-box-at0220 ∷ᵃ lem-CXcb-box-at03102132 ∷ᵃ lem-VPQ-at0213243140 ∷ᵃ lem-box-tQ-at0213213440 ∷ᵃ lem-box-tQ-at02233440 ∷ᵃ lem-box-tQ-at022440 ∷ᵃ lem-tP-at0214203143 ∷ᵃ lem-tP-at022330 ∷ᵃ lem-tP-at022440 ∷ᵃ lem-tP-at14213243 ∷ᵃ nil
lem-VPQ-at0214213043 : _
lem-VPQ-at0214213043 = D010.lem-VPQ-at0214213043 sD010
lem-VPQ-at0210233441 : _
lem-VPQ-at0210233441 = D010.lem-VPQ-at0210233441 sD010
lem-CXbc-box-at122441 : _
lem-CXbc-box-at122441 = D010.lem-CXbc-box-at122441 sD010
lem-CXcb-box-at122441 : _
lem-CXcb-box-at122441 = D010.lem-CXcb-box-at122441 sD010
lem-VPQ-at12233441 : _
lem-VPQ-at12233441 = D010.lem-VPQ-at12233441 sD010
lem-CSu-box-2-at0210243143 : _
lem-CSu-box-2-at0210243143 = D010.lem-CSu-box-2-at0210243143 sD010
lem-CXbc-box-at14213243 : _
lem-CXbc-box-at14213243 = D010.lem-CXbc-box-at14213243 sD010
lem-CXcb-box-at14213243 : _
lem-CXcb-box-at14213243 = D010.lem-CXcb-box-at14213243 sD010
lem-P-box-at143143 : _
lem-P-box-at143143 = D010.lem-P-box-at143143 sD010
lem-VPQ-at143143 : _
lem-VPQ-at143143 = D010.lem-VPQ-at143143 sD010
lem-VPQ-at233442 : _
lem-VPQ-at233442 = D010.lem-VPQ-at233442 sD010
lem-CXbc-box-at0210243143 : _
lem-CXbc-box-at0210243143 = D010.lem-CXbc-box-at0210243143 sD010
lem-CXcb-box-at0210243143 : _
lem-CXcb-box-at0210243143 = D010.lem-CXcb-box-at0210243143 sD010
lem-QVQ-at0210213443 : _
lem-QVQ-at0210213443 = D010.lem-QVQ-at0210213443 sD010
lem-CXbc-box-at243243 : _
lem-CXbc-box-at243243 = D010.lem-CXbc-box-at243243 sD010
lem-CXcb-box-at243243 : _
lem-CXcb-box-at243243 = D010.lem-CXcb-box-at243243 sD010
lem-CXbc-box-at1441 : _
lem-CXbc-box-at1441 = D010.lem-CXbc-box-at1441 sD010
lem-CXcb-box-at1441 : _
lem-CXcb-box-at1441 = D010.lem-CXcb-box-at1441 sD010
lem-QVQ-at14233241 : _
lem-QVQ-at14233241 = D010.lem-QVQ-at14233241 sD010
lem-VPQ-at12213443 : _
lem-VPQ-at12213443 = D010.lem-VPQ-at12213443 sD010
lem-CXbc-box-at0314213042 : _
lem-CXbc-box-at0314213042 = D010.lem-CXbc-box-at0314213042 sD010
lem-CXcb-box-at0314213042 : _
lem-CXcb-box-at0314213042 = D010.lem-CXcb-box-at0314213042 sD010
lem-VPQ-at0213203441 : _
lem-VPQ-at0213203441 = D010.lem-VPQ-at0213203441 sD010
lem-P-box-at0210233441 : _
lem-P-box-at0210233441 = D010.lem-P-box-at0210233441 sD010
lem-CXbc-box-at0314203142 : _
lem-CXbc-box-at0314203142 = D010.lem-CXbc-box-at0314203142 sD010
lem-CXcb-box-at0314203142 : _
lem-CXcb-box-at0314203142 = D010.lem-CXcb-box-at0314203142 sD010
lem-VPQ-at0314213042 : _
lem-VPQ-at0314213042 = D010.lem-VPQ-at0314213042 sD010
lem-t-cP-at0314213042 : _
lem-t-cP-at0314213042 = D010.lem-t-cP-at0314213042 sD010
lem-CXbc-box-at0214213043 : _
lem-CXbc-box-at0214213043 = D010.lem-CXbc-box-at0214213043 sD010
lem-CXcb-box-at0214213043 : _
lem-CXcb-box-at0214213043 = D010.lem-CXcb-box-at0214213043 sD010
lem-P-box-at243243 : _
lem-P-box-at243243 = D010.lem-P-box-at243243 sD010
lem-CXbc-box-at1331 : _
lem-CXbc-box-at1331 = D010.lem-CXbc-box-at1331 sD010
lem-CXcb-box-at1331 : _
lem-CXcb-box-at1331 = D010.lem-CXcb-box-at1331 sD010
lem-QVQ-at032032 : _
lem-QVQ-at032032 = D010.lem-QVQ-at032032 sD010
lem-CXbc-box-at0312243140 : _
lem-CXbc-box-at0312243140 = D010.lem-CXbc-box-at0312243140 sD010
lem-CXcb-box-at0312243140 : _
lem-CXcb-box-at0312243140 = D010.lem-CXcb-box-at0312243140 sD010
lem-CXbc-box-at0312213440 : _
lem-CXbc-box-at0312213440 = D010.lem-CXbc-box-at0312213440 sD010
lem-CXcb-box-at0312213440 : _
lem-CXcb-box-at0312213440 = D010.lem-CXcb-box-at0312213440 sD010
lem-P-box-at0312243140 : _
lem-P-box-at0312243140 = D010.lem-P-box-at0312243140 sD010
lem-VPQ-at0312243140 : _
lem-VPQ-at0312243140 = D010.lem-VPQ-at0312243140 sD010
lem-CXbc-box-at132132 : _
lem-CXbc-box-at132132 = D010.lem-CXbc-box-at132132 sD010
lem-CXcb-box-at132132 : _
lem-CXcb-box-at132132 = D010.lem-CXcb-box-at132132 sD010
lem-P-box-at0210243143 : _
lem-P-box-at0210243143 = D010.lem-P-box-at0210243143 sD010
lem-CXbc-box-at022330 : _
lem-CXbc-box-at022330 = D010.lem-CXbc-box-at022330 sD010
lem-CXcb-box-at022330 : _
lem-CXcb-box-at022330 = D010.lem-CXcb-box-at022330 sD010
lem-QVQ-at0220 : _
lem-QVQ-at0220 = D010.lem-QVQ-at0220 sD010
lem-SWbc-box-at0213243140 : _
lem-SWbc-box-at0213243140 = D010.lem-SWbc-box-at0213243140 sD010
lem-CXbc-box-at0213213440 : _
lem-CXbc-box-at0213213440 = D010.lem-CXbc-box-at0213213440 sD010
lem-CXcb-box-at0213213440 : _
lem-CXcb-box-at0213213440 = D010.lem-CXcb-box-at0213213440 sD010
lem-QVQ-at0213243140 : _
lem-QVQ-at0213243140 = D010.lem-QVQ-at0213243140 sD010
lem-SWbc-box-at0220 : _
lem-SWbc-box-at0220 = D010.lem-SWbc-box-at0220 sD010
lem-P-box-at022330 : _
lem-P-box-at022330 = D010.lem-P-box-at022330 sD010
lem-VPQ-at022330 : _
lem-VPQ-at022330 = D010.lem-VPQ-at022330 sD010
lem-CXbc-box-at122331 : _
lem-CXbc-box-at122331 = D010.lem-CXbc-box-at122331 sD010
lem-CXcb-box-at122331 : _
lem-CXcb-box-at122331 = D010.lem-CXcb-box-at122331 sD010
lem-P-box-at14213243 : _
lem-P-box-at14213243 = D010.lem-P-box-at14213243 sD010
lem-VPQ-at14213243 : _
lem-VPQ-at14213243 = D010.lem-VPQ-at14213243 sD010
lem-CXbc-box-at12233441 : _
lem-CXbc-box-at12233441 = D010.lem-CXbc-box-at12233441 sD010
lem-CXcb-box-at12233441 : _
lem-CXcb-box-at12233441 = D010.lem-CXcb-box-at12233441 sD010
lem-P-box-at12233441 : _
lem-P-box-at12233441 = D010.lem-P-box-at12233441 sD010
lem-P-box-at122441 : _
lem-P-box-at122441 = D010.lem-P-box-at122441 sD010
lem-CXbc-box-at2332 : _
lem-CXbc-box-at2332 = D010.lem-CXbc-box-at2332 sD010
lem-CXcb-box-at2332 : _
lem-CXcb-box-at2332 = D010.lem-CXcb-box-at2332 sD010
lem-SWbc-box-at03102132 : _
lem-SWbc-box-at03102132 = D010.lem-SWbc-box-at03102132 sD010
lem-VPQ-at0214203143 : _
lem-VPQ-at0214203143 = D010.lem-VPQ-at0214203143 sD010
lem-CXbc-box-at02233440 : _
lem-CXbc-box-at02233440 = D010.lem-CXbc-box-at02233440 sD010
lem-CXcb-box-at02233440 : _
lem-CXcb-box-at02233440 = D010.lem-CXcb-box-at02233440 sD010
lem-VPQ-at022440 : _
lem-VPQ-at022440 = D010.lem-VPQ-at022440 sD010
lem-CXbc-box-at022440 : _
lem-CXbc-box-at022440 = D010.lem-CXbc-box-at022440 sD010
sD011 : SD011
sD011 = (λ c → lem-comm-CS13-TOFF024 (lit c)) ∷ᵃ (λ c → lem-comm-CS24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-TOFF024 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-TOFF014 (lit c)) ∷ᵃ (λ c → lem-comm-CSd24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-CX02-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-CX04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CX12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX14-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CX21-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX24-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-CX42-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-CZ04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CZ04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CZ24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF014-CSd23 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF024-CSd13 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF204-CSd13 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF312-CSd04 (lit c)) ∷ᵃ (λ c → lem-comm-CS02-TOFF314 (lit c)) ∷ᵃ (λ c → lem-comm-CS03-TOFF214 (lit c)) ∷ᵃ (λ c → lem-comm-CS04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CS12-TOFF304 (lit c)) ∷ᵃ (λ c → lem-comm-CS13-TOFF204 (lit c)) ∷ᵃ (λ c → lem-comm-CS14-TOFF203 (lit c)) ∷ᵃ (λ c → lem-comm-CS23-TOFF014 (lit c)) ∷ᵃ (λ c → lem-comm-CSd02-TOFF314 (lit c)) ∷ᵃ (λ c → lem-comm-CSd03-TOFF214 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-TOFF304 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-TOFF204 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-TOFF203 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-TOFF302 (lit c)) ∷ᵃ (λ c → lem-comm-CSd24-TOFF301 (lit c)) ∷ᵃ (λ c → lem-comm-CX03-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CX40-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CX41-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CZ02-TOFF314 (lit c)) ∷ᵃ (λ c → lem-comm-CZ12-TOFF304 (lit c)) ∷ᵃ (λ c → lem-comm-CZ13-TOFF024 (lit c)) ∷ᵃ (λ c → lem-comm-CZ14-TOFF302 (lit c)) ∷ᵃ (λ c → lem-comm-CZ24-TOFF301 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF213-CSd04 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF304-CSd12 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF314-CSd02 (lit c)) ∷ᵃ (λ c → lem-comm-CS14-TOFF302 (lit c)) ∷ᵃ (λ c → lem-comm-CX20-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF302-CSd14 (lit c)) ∷ᵃ lem-box-tQ ∷ᵃ lem-box-tQ-at0210233441 ∷ᵃ lem-box-tQ-at0310243142 ∷ᵃ lem-box-tQ-at0314203142 ∷ᵃ lem-box-tQ-at0314213042 ∷ᵃ lem-box-tQ-at033440 ∷ᵃ lem-box-tQ-at12213443 ∷ᵃ lem-box-tQ-at143143 ∷ᵃ lem-box-tQ-at1441 ∷ᵃ lem-box-tQ-at233442 ∷ᵃ lem-box-tQ-at2442 ∷ᵃ lem-box-tQ-at3443 ∷ᵃ lem-tP-at0310243142 ∷ᵃ lem-tP-at0314203142 ∷ᵃ lem-tP-at0314213042 ∷ᵃ lem-tP-at12213443 ∷ᵃ lem-tP-at233442 ∷ᵃ lem-CXbc-box-at0310213442 ∷ᵃ lem-CXbc-box-at14233241 ∷ᵃ lem-CXcb-box-at0310213442 ∷ᵃ lem-CXcb-box-at14233241 ∷ᵃ lem-box-tQ-at02102441 ∷ᵃ lem-box-tQ-at02142041 ∷ᵃ lem-box-tQ-at02233440 ∷ᵃ lem-box-tQ-at022440 ∷ᵃ lem-box-tQ-at0310243241 ∷ᵃ lem-box-tQ-at031031 ∷ᵃ lem-box-tQ-at03103441 ∷ᵃ lem-box-tQ-at0312203441 ∷ᵃ lem-box-tQ-at0312243041 ∷ᵃ lem-box-tQ-at0314213240 ∷ᵃ lem-box-tQ-at03143041 ∷ᵃ lem-box-tQ-at03143140 ∷ᵃ lem-box-tQ-at03243240 ∷ᵃ lem-tP-at02102441 ∷ᵃ lem-tP-at02233440 ∷ᵃ lem-tP-at0310243241 ∷ᵃ lem-tP-at031031 ∷ᵃ lem-tP-at03103441 ∷ᵃ lem-tP-at0312203441 ∷ᵃ lem-tP-at0312243041 ∷ᵃ lem-tP-at0314213240 ∷ᵃ lem-tP-at03143140 ∷ᵃ lem-tP-at03243240 ∷ᵃ lem-tP-at033440 ∷ᵃ lem-tP-at12243143 ∷ᵃ lem-tP-at1441 ∷ᵃ lem-tP-at2442 ∷ᵃ nil
lem-CXcb-box-at022440 : _
lem-CXcb-box-at022440 = D011.lem-CXcb-box-at022440 sD011
lem-VPQ-at02233440 : _
lem-VPQ-at02233440 = D011.lem-VPQ-at02233440 sD011
lem-VPQ-at1441 : _
lem-VPQ-at1441 = D011.lem-VPQ-at1441 sD011
lem-CXbc-box-at0210233441 : _
lem-CXbc-box-at0210233441 = D011.lem-CXbc-box-at0210233441 sD011
lem-CXcb-box-at0210233441 : _
lem-CXcb-box-at0210233441 = D011.lem-CXcb-box-at0210233441 sD011
lem-VPQ-at02102441 : _
lem-VPQ-at02102441 = D011.lem-VPQ-at02102441 sD011
lem-CXbc-box-at02102441 : _
lem-CXbc-box-at02102441 = D011.lem-CXbc-box-at02102441 sD011
lem-CXcb-box-at02102441 : _
lem-CXcb-box-at02102441 = D011.lem-CXcb-box-at02102441 sD011
lem-CXbc-box-at233442 : _
lem-CXbc-box-at233442 = D011.lem-CXbc-box-at233442 sD011
lem-CXcb-box-at233442 : _
lem-CXcb-box-at233442 = D011.lem-CXcb-box-at233442 sD011
lem-VPQ-at2442 : _
lem-VPQ-at2442 = D011.lem-VPQ-at2442 sD011
lem-CXbc-box-at2442 : _
lem-CXbc-box-at2442 = D011.lem-CXbc-box-at2442 sD011
lem-CXcb-box-at2442 : _
lem-CXcb-box-at2442 = D011.lem-CXcb-box-at2442 sD011
lem-CXbc-box-at143143 : _
lem-CXbc-box-at143143 = D011.lem-CXbc-box-at143143 sD011
lem-CXcb-box-at143143 : _
lem-CXcb-box-at143143 = D011.lem-CXcb-box-at143143 sD011
lem-CXbc-box-at12213443 : _
lem-CXbc-box-at12213443 = D011.lem-CXbc-box-at12213443 sD011
lem-CXcb-box-at12213443 : _
lem-CXcb-box-at12213443 = D011.lem-CXcb-box-at12213443 sD011
lem-VPQ-at12243143 : _
lem-VPQ-at12243143 = D011.lem-VPQ-at12243143 sD011
lem-SWbc-box-at14233241 : _
lem-SWbc-box-at14233241 = D011.lem-SWbc-box-at14233241 sD011
lem-CXbc-box-at03143140 : _
lem-CXbc-box-at03143140 = D011.lem-CXbc-box-at03143140 sD011
lem-CXcb-box-at03143140 : _
lem-CXcb-box-at03143140 = D011.lem-CXcb-box-at03143140 sD011
lem-VPQ-at0314213240 : _
lem-VPQ-at0314213240 = D011.lem-VPQ-at0314213240 sD011
lem-CXbc-box-at0314213240 : _
lem-CXbc-box-at0314213240 = D011.lem-CXbc-box-at0314213240 sD011
lem-CXcb-box-at0314213240 : _
lem-CXcb-box-at0314213240 = D011.lem-CXcb-box-at0314213240 sD011
lem-VPQ-at03143140 : _
lem-VPQ-at03143140 = D011.lem-VPQ-at03143140 sD011
lem-VPQ-at03243240 : _
lem-VPQ-at03243240 = D011.lem-VPQ-at03243240 sD011
lem-CXbc-box-at033440 : _
lem-CXbc-box-at033440 = D011.lem-CXbc-box-at033440 sD011
lem-CXcb-box-at033440 : _
lem-CXcb-box-at033440 = D011.lem-CXcb-box-at033440 sD011
lem-CXbc-box-at03243240 : _
lem-CXbc-box-at03243240 = D011.lem-CXbc-box-at03243240 sD011
lem-CXcb-box-at03243240 : _
lem-CXcb-box-at03243240 = D011.lem-CXcb-box-at03243240 sD011
lem-VPQ-at033440 : _
lem-VPQ-at033440 = D011.lem-VPQ-at033440 sD011
lem-CXbc-box-at03103441 : _
lem-CXbc-box-at03103441 = D011.lem-CXbc-box-at03103441 sD011
lem-CXcb-box-at03103441 : _
lem-CXcb-box-at03103441 = D011.lem-CXcb-box-at03103441 sD011
lem-VPQ-at0310243241 : _
lem-VPQ-at0310243241 = D011.lem-VPQ-at0310243241 sD011
lem-CXbc-box-at0310243241 : _
lem-CXbc-box-at0310243241 = D011.lem-CXbc-box-at0310243241 sD011
lem-CXcb-box-at0310243241 : _
lem-CXcb-box-at0310243241 = D011.lem-CXcb-box-at0310243241 sD011
lem-VPQ-at03103441 : _
lem-VPQ-at03103441 = D011.lem-VPQ-at03103441 sD011
lem-CXbc-box-at0310243142 : _
lem-CXbc-box-at0310243142 = D011.lem-CXbc-box-at0310243142 sD011
lem-CXcb-box-at0310243142 : _
lem-CXcb-box-at0310243142 = D011.lem-CXcb-box-at0310243142 sD011
lem-SWbc-box-at0310213442 : _
lem-SWbc-box-at0310213442 = D011.lem-SWbc-box-at0310213442 sD011
lem-CXbc-box-at0312203441 : _
lem-CXbc-box-at0312203441 = D011.lem-CXbc-box-at0312203441 sD011
lem-CXcb-box-at0312203441 : _
lem-CXcb-box-at0312203441 = D011.lem-CXcb-box-at0312203441 sD011
lem-VPQ-at0312243041 : _
lem-VPQ-at0312243041 = D011.lem-VPQ-at0312243041 sD011
lem-CXbc-box-at0312243041 : _
lem-CXbc-box-at0312243041 = D011.lem-CXbc-box-at0312243041 sD011
lem-CXcb-box-at0312243041 : _
lem-CXcb-box-at0312243041 = D011.lem-CXcb-box-at0312243041 sD011
lem-VPQ-at0312203441 : _
lem-VPQ-at0312203441 = D011.lem-VPQ-at0312203441 sD011
lem-CXbc-box-at3443 : _
lem-CXbc-box-at3443 = D011.lem-CXbc-box-at3443 sD011
lem-CXcb-box-at3443 : _
lem-CXcb-box-at3443 = D011.lem-CXcb-box-at3443 sD011
lem-CXbc-box-at031031 : _
lem-CXbc-box-at031031 = D011.lem-CXbc-box-at031031 sD011
lem-CXcb-box-at031031 : _
lem-CXcb-box-at031031 = D011.lem-CXcb-box-at031031 sD011
lem-VPQ-at031031 : _
lem-VPQ-at031031 = D011.lem-VPQ-at031031 sD011
lem-CXbc-box-at03143041 : _
lem-CXbc-box-at03143041 = D011.lem-CXbc-box-at03143041 sD011
lem-CXcb-box-at03143041 : _
lem-CXcb-box-at03143041 = D011.lem-CXcb-box-at03143041 sD011
lem-CXbc-box-at02142041 : _
lem-CXbc-box-at02142041 = D011.lem-CXbc-box-at02142041 sD011
sD008 : SD008
sD008 = (λ c → lem-comm-CZ12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CZ13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CZ23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CZ03-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CZ02-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-CZ23-TOFF401 (lit c)) ∷ᵃ lem-box-tQ-at0410213243 ∷ᵃ lem-box-tQ-at04203243 ∷ᵃ lem-tP-at0410213243 ∷ᵃ lem-tP-at04203243 ∷ᵃ lem-cQ-at02142140 ∷ᵃ lem-cQ-at0410233142 ∷ᵃ lem-cQ-at0410233241 ∷ᵃ lem-cQ-at041041 ∷ᵃ lem-cQ-at0412213043 ∷ᵃ lem-cQ-at04122140 ∷ᵃ lem-cQ-at0412233041 ∷ᵃ lem-cQ-at0412233140 ∷ᵃ lem-cQ-at0413203142 ∷ᵃ lem-cQ-at0413203241 ∷ᵃ lem-cQ-at0413213042 ∷ᵃ lem-cQ-at0413213240 ∷ᵃ lem-cQ-at04133140 ∷ᵃ lem-cQ-at04233240 ∷ᵃ lem-cQ-at0440 ∷ᵃ lem-tP-at0310213442 ∷ᵃ nil
lem-box-tQ-at0412233041 : _
lem-box-tQ-at0412233041 = D008.lem-box-tQ-at0412233041 sD008
lem-box-tQ-at041041 : _
lem-box-tQ-at041041 = D008.lem-box-tQ-at041041 sD008
lem-box-tQ-at0410233241 : _
lem-box-tQ-at0410233241 = D008.lem-box-tQ-at0410233241 sD008
lem-tP-at0410233241 : _
lem-tP-at0410233241 = D008.lem-tP-at0410233241 sD008
lem-tP-at0412213043 : _
lem-tP-at0412213043 = D008.lem-tP-at0412213043 sD008
lem-box-tQ-at0413213240 : _
lem-box-tQ-at0413213240 = D008.lem-box-tQ-at0413213240 sD008
lem-box-tQ-at04233240 : _
lem-box-tQ-at04233240 = D008.lem-box-tQ-at04233240 sD008
lem-box-tQ-at0440 : _
lem-box-tQ-at0440 = D008.lem-box-tQ-at0440 sD008
lem-tP-at0440 : _
lem-tP-at0440 = D008.lem-tP-at0440 sD008
lem-box-tQ-at0413203142 : _
lem-box-tQ-at0413203142 = D008.lem-box-tQ-at0413203142 sD008
lem-tP-at02142140 : _
lem-tP-at02142140 = D008.lem-tP-at02142140 sD008
lem-box-tQ-at0413213042 : _
lem-box-tQ-at0413213042 = D008.lem-box-tQ-at0413213042 sD008
lem-tP-at0413203142 : _
lem-tP-at0413203142 = D008.lem-tP-at0413203142 sD008
lem-tP-at0413213240 : _
lem-tP-at0413213240 = D008.lem-tP-at0413213240 sD008
lem-box-tQ-at0412233140 : _
lem-box-tQ-at0412233140 = D008.lem-box-tQ-at0412233140 sD008
lem-box-tQ-at0410233142 : _
lem-box-tQ-at0410233142 = D008.lem-box-tQ-at0410233142 sD008
lem-tP-at0410233142 : _
lem-tP-at0410233142 = D008.lem-tP-at0410233142 sD008
lem-box-tQ-at04122140 : _
lem-box-tQ-at04122140 = D008.lem-box-tQ-at04122140 sD008
lem-tP-at0412233140 : _
lem-tP-at0412233140 = D008.lem-tP-at0412233140 sD008
lem-box-tQ-at0413203241 : _
lem-box-tQ-at0413203241 = D008.lem-box-tQ-at0413203241 sD008
lem-tP-at0413203241 : _
lem-tP-at0413203241 = D008.lem-tP-at0413203241 sD008
lem-tP-at04122140 : _
lem-tP-at04122140 = D008.lem-tP-at04122140 sD008
lem-CSdu-box-2-at04203243 : _
lem-CSdu-box-2-at04203243 = D008.lem-CSdu-box-2-at04203243 sD008
lem-Su-box-at04203243 : _
lem-Su-box-at04203243 = D008.lem-Su-box-at04203243 sD008
lem-box-tQ-at04133140 : _
lem-box-tQ-at04133140 = D008.lem-box-tQ-at04133140 sD008
sD012 : SD012
sD012 = (λ c → lem-comm-CS03-TOFF412 (lit c)) ∷ᵃ (λ c → lem-comm-CSd03-TOFF412 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-TOFF403 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-TOFF014 (lit c)) ∷ᵃ (λ c → lem-comm-CX02-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-CX12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX21-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX31-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CZ03-TOFF412 (lit c)) ∷ᵃ (λ c → lem-comm-CZ04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CZ04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CZ14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF014-CSd23 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF204-CSd13 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF312-CSd04 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF412-CSd03 (lit c)) ∷ᵃ (λ c → lem-comm-CS04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CS04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CS12-TOFF304 (lit c)) ∷ᵃ (λ c → lem-comm-CS13-TOFF204 (lit c)) ∷ᵃ (λ c → lem-comm-CS14-TOFF203 (lit c)) ∷ᵃ (λ c → lem-comm-CS23-TOFF014 (lit c)) ∷ᵃ (λ c → lem-comm-CSd02-TOFF314 (lit c)) ∷ᵃ (λ c → lem-comm-CSd03-TOFF214 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-TOFF304 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-TOFF204 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-TOFF203 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-TOFF302 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-TOFF401 (lit c)) ∷ᵃ (λ c → lem-comm-CSd24-TOFF301 (lit c)) ∷ᵃ (λ c → lem-comm-CX03-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CX30-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CX40-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CX41-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CZ02-TOFF314 (lit c)) ∷ᵃ (λ c → lem-comm-CZ12-TOFF304 (lit c)) ∷ᵃ (λ c → lem-comm-CZ12-TOFF403 (lit c)) ∷ᵃ (λ c → lem-comm-CZ13-TOFF204 (lit c)) ∷ᵃ (λ c → lem-comm-CZ14-TOFF302 (lit c)) ∷ᵃ (λ c → lem-comm-CZ23-TOFF014 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF213-CSd04 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF214-CSd03 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF304-CSd12 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF314-CSd02 (lit c)) ∷ᵃ (λ c → lem-comm-CK40-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CS13-TOFF402 (lit c)) ∷ᵃ (λ c → lem-comm-CS14-TOFF302 (lit c)) ∷ᵃ (λ c → lem-comm-CSd02-TOFF413 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-TOFF402 (lit c)) ∷ᵃ (λ c → lem-comm-CX20-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-CZ13-TOFF402 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF402-CSd13 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF413-CSd02 (lit c)) ∷ᵃ (λ c → lem-comm-CS02-TOFF413 (lit c)) ∷ᵃ (λ c → lem-comm-CS12-TOFF403 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF403-CSd12 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF203-CSd14 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF302-CSd14 (lit c)) ∷ᵃ lem-box-tQ-at033440 ∷ᵃ lem-box-tQ-at2442 ∷ᵃ lem-CXbc-box-at021021 ∷ᵃ lem-CXbc-box-at0210213443 ∷ᵃ lem-CXbc-box-at0214233041 ∷ᵃ lem-CXbc-box-at0410213243 ∷ᵃ lem-CXcb-box-at021021 ∷ᵃ lem-CXcb-box-at0210213443 ∷ᵃ lem-CXcb-box-at0214233041 ∷ᵃ lem-CXcb-box-at0410213243 ∷ᵃ lem-VPQ-at0213243041 ∷ᵃ lem-VPQ-at0214233041 ∷ᵃ lem-VPQ-at0310213442 ∷ᵃ lem-box-tQ-at02102331 ∷ᵃ lem-box-tQ-at02102441 ∷ᵃ lem-box-tQ-at02132031 ∷ᵃ lem-box-tQ-at02132130 ∷ᵃ lem-box-tQ-at02142041 ∷ᵃ lem-box-tQ-at0310243241 ∷ᵃ lem-box-tQ-at031031 ∷ᵃ lem-box-tQ-at03122031 ∷ᵃ lem-box-tQ-at03122130 ∷ᵃ lem-box-tQ-at0312243041 ∷ᵃ lem-box-tQ-at0314203241 ∷ᵃ lem-box-tQ-at03143041 ∷ᵃ lem-box-tQ-at03243042 ∷ᵃ lem-box-tQ-at04103143 ∷ᵃ lem-box-tQ-at04122041 ∷ᵃ lem-box-tQ-at142142 ∷ᵃ lem-tP-at02102331 ∷ᵃ lem-tP-at02102441 ∷ᵃ lem-tP-at02132031 ∷ᵃ lem-tP-at02132130 ∷ᵃ lem-tP-at0214203143 ∷ᵃ lem-tP-at02142041 ∷ᵃ lem-tP-at0310243241 ∷ᵃ lem-tP-at031031 ∷ᵃ lem-tP-at03122031 ∷ᵃ lem-tP-at03122130 ∷ᵃ lem-tP-at0312243041 ∷ᵃ lem-tP-at0314203241 ∷ᵃ lem-tP-at03143041 ∷ᵃ lem-tP-at03243042 ∷ᵃ lem-tP-at033440 ∷ᵃ lem-tP-at04103143 ∷ᵃ lem-tP-at04122041 ∷ᵃ lem-tP-at0412233041 ∷ᵃ lem-tP-at04233042 ∷ᵃ lem-tP-at142142 ∷ᵃ lem-tP-at2442 ∷ᵃ lem-box-tQ-at0410233241 ∷ᵃ lem-box-tQ-at041041 ∷ᵃ lem-box-tQ-at0412233041 ∷ᵃ lem-box-tQ-at0413203142 ∷ᵃ lem-box-tQ-at0413213042 ∷ᵃ lem-box-tQ-at04233240 ∷ᵃ lem-box-tQ-at0440 ∷ᵃ lem-tP-at02142140 ∷ᵃ lem-tP-at0410233241 ∷ᵃ lem-tP-at0412213043 ∷ᵃ lem-tP-at0413203142 ∷ᵃ lem-tP-at0440 ∷ᵃ nil
lem-CXcb-box-at02142041 : _
lem-CXcb-box-at02142041 = D012.lem-CXcb-box-at02142041 sD012
lem-QVQ-at0214233041 : _
lem-QVQ-at0214233041 = D012.lem-QVQ-at0214233041 sD012
lem-CXbc-box-at0314203241 : _
lem-CXbc-box-at0314203241 = D012.lem-CXbc-box-at0314203241 sD012
lem-CXcb-box-at0314203241 : _
lem-CXcb-box-at0314203241 = D012.lem-CXcb-box-at0314203241 sD012
lem-SWbc-box-at0210213443 : _
lem-SWbc-box-at0210213443 = D012.lem-SWbc-box-at0210213443 sD012
lem-SWbc-box-at0214233041 : _
lem-SWbc-box-at0214233041 = D012.lem-SWbc-box-at0214233041 sD012
lem-CXbc-box-at02132130 : _
lem-CXbc-box-at02132130 = D012.lem-CXbc-box-at02132130 sD012
lem-CXcb-box-at02132130 : _
lem-CXcb-box-at02132130 = D012.lem-CXcb-box-at02132130 sD012
lem-VPQ-at03143041 : _
lem-VPQ-at03143041 = D012.lem-VPQ-at03143041 sD012
lem-VPQ-at02132031 : _
lem-VPQ-at02132031 = D012.lem-VPQ-at02132031 sD012
lem-QVQ-at0310213442 : _
lem-QVQ-at0310213442 = D012.lem-QVQ-at0310213442 sD012
lem-CXbc-box-at02132031 : _
lem-CXbc-box-at02132031 = D012.lem-CXbc-box-at02132031 sD012
lem-CXcb-box-at02132031 : _
lem-CXcb-box-at02132031 = D012.lem-CXcb-box-at02132031 sD012
lem-VPQ-at02132130 : _
lem-VPQ-at02132130 = D012.lem-VPQ-at02132130 sD012
lem-QVQ-at0213243041 : _
lem-QVQ-at0213243041 = D012.lem-QVQ-at0213243041 sD012
lem-CXbc-box-at03122130 : _
lem-CXbc-box-at03122130 = D012.lem-CXbc-box-at03122130 sD012
lem-CXcb-box-at03122130 : _
lem-CXcb-box-at03122130 = D012.lem-CXcb-box-at03122130 sD012
lem-VPQ-at03122031 : _
lem-VPQ-at03122031 = D012.lem-VPQ-at03122031 sD012
lem-CXbc-box-at03122031 : _
lem-CXbc-box-at03122031 = D012.lem-CXbc-box-at03122031 sD012
lem-CXcb-box-at03122031 : _
lem-CXcb-box-at03122031 = D012.lem-CXcb-box-at03122031 sD012
lem-VPQ-at03122130 : _
lem-VPQ-at03122130 = D012.lem-VPQ-at03122130 sD012
lem-VPQ-at02142041 : _
lem-VPQ-at02142041 = D012.lem-VPQ-at02142041 sD012
lem-VPQ-at0314203241 : _
lem-VPQ-at0314203241 = D012.lem-VPQ-at0314203241 sD012
lem-SWbc-box-at021021 : _
lem-SWbc-box-at021021 = D012.lem-SWbc-box-at021021 sD012
lem-VPQ-at02102331 : _
lem-VPQ-at02102331 = D012.lem-VPQ-at02102331 sD012
lem-CXbc-box-at142142 : _
lem-CXbc-box-at142142 = D012.lem-CXbc-box-at142142 sD012
lem-CXcb-box-at142142 : _
lem-CXcb-box-at142142 = D012.lem-CXcb-box-at142142 sD012
lem-VPQ-at03243042 : _
lem-VPQ-at03243042 = D012.lem-VPQ-at03243042 sD012
lem-CXbc-box-at02102331 : _
lem-CXbc-box-at02102331 = D012.lem-CXbc-box-at02102331 sD012
lem-CXcb-box-at02102331 : _
lem-CXcb-box-at02102331 = D012.lem-CXcb-box-at02102331 sD012
lem-VPQ-at142142 : _
lem-VPQ-at142142 = D012.lem-VPQ-at142142 sD012
lem-CXbc-box-at04122041 : _
lem-CXbc-box-at04122041 = D012.lem-CXbc-box-at04122041 sD012
lem-CXcb-box-at04122041 : _
lem-CXcb-box-at04122041 = D012.lem-CXcb-box-at04122041 sD012
lem-VPQ-at0412233041 : _
lem-VPQ-at0412233041 = D012.lem-VPQ-at0412233041 sD012
lem-VPQ-at04122041 : _
lem-VPQ-at04122041 = D012.lem-VPQ-at04122041 sD012
lem-SWbc-box-at0410213243 : _
lem-SWbc-box-at0410213243 = D012.lem-SWbc-box-at0410213243 sD012
lem-VPQ-at04103143 : _
lem-VPQ-at04103143 = D012.lem-VPQ-at04103143 sD012
lem-VPQ-at04233042 : _
lem-VPQ-at04233042 = D012.lem-VPQ-at04233042 sD012
lem-CXbc-box-at0412233041 : _
lem-CXbc-box-at0412233041 = D012.lem-CXbc-box-at0412233041 sD012
lem-CXcb-box-at0412233041 : _
lem-CXcb-box-at0412233041 = D012.lem-CXcb-box-at0412233041 sD012
lem-CXbc-box-at041041 : _
lem-CXbc-box-at041041 = D012.lem-CXbc-box-at041041 sD012
lem-CXcb-box-at041041 : _
lem-CXcb-box-at041041 = D012.lem-CXcb-box-at041041 sD012
lem-VPQ-at0410233241 : _
lem-VPQ-at0410233241 = D012.lem-VPQ-at0410233241 sD012
lem-VPQ-at0412213043 : _
lem-VPQ-at0412213043 = D012.lem-VPQ-at0412213043 sD012
lem-CXbc-box-at04233240 : _
lem-CXbc-box-at04233240 = D012.lem-CXbc-box-at04233240 sD012
lem-CXcb-box-at04233240 : _
lem-CXcb-box-at04233240 = D012.lem-CXcb-box-at04233240 sD012
lem-VPQ-at0440 : _
lem-VPQ-at0440 = D012.lem-VPQ-at0440 sD012
lem-CXbc-box-at0413203142 : _
lem-CXbc-box-at0413203142 = D012.lem-CXbc-box-at0413203142 sD012
lem-CXcb-box-at0413203142 : _
lem-CXcb-box-at0413203142 = D012.lem-CXcb-box-at0413203142 sD012
lem-VPQ-at02142140 : _
lem-VPQ-at02142140 = D012.lem-VPQ-at02142140 sD012
lem-CXbc-box-at0413213042 : _
lem-CXbc-box-at0413213042 = D012.lem-CXbc-box-at0413213042 sD012
lem-CXcb-box-at0413213042 : _
lem-CXcb-box-at0413213042 = D012.lem-CXcb-box-at0413213042 sD012
lem-VPQ-at0413203142 : _
lem-VPQ-at0413203142 = D012.lem-VPQ-at0413203142 sD012
lem-CXbc-box-at0440 : _
lem-CXbc-box-at0440 = D012.lem-CXbc-box-at0440 sD012
lem-CXcb-box-at0440 : _
lem-CXcb-box-at0440 = D012.lem-CXcb-box-at0440 sD012
sD014 : SD014
sD014 = lem-nat-SWbc-at0213243140 ∷ᵃ lem-nat-SWbc-at03102132 ∷ᵃ lem-nat-SWbc-at032032 ∷ᵃ lem-nat-SWbc-at04203243 ∷ᵃ lem-nat-SWbc-at13243142 ∷ᵃ lem-nat-SWbc-at13243241 ∷ᵃ lem-nat-SWbc-at14233142 ∷ᵃ lem-tP-at021021 ∷ᵃ lem-tP-at0210213443 ∷ᵃ lem-tP-at0213243140 ∷ᵃ lem-tP-at0220 ∷ᵃ lem-tP-at03102132 ∷ᵃ lem-tP-at032032 ∷ᵃ lem-tP-at0410213243 ∷ᵃ lem-tP-at04203243 ∷ᵃ lem-tP-at13243142 ∷ᵃ lem-tP-at13243241 ∷ᵃ lem-tP-at14233142 ∷ᵃ lem-tP-at14233241 ∷ᵃ lem-nat-SWbc-at0310213442 ∷ᵃ lem-nat-SWbc-at14233241 ∷ᵃ lem-nat-SWbc-at0220 ∷ᵃ lem-CSdu-box-1 ∷ᵃ lem-CSdu-box-2 ∷ᵃ lem-CSdu-box-2-at0210243143 ∷ᵃ lem-CSdu-box-2-at122441 ∷ᵃ lem-CSdu-box-2-at243243 ∷ᵃ lem-CSu-box-1 ∷ᵃ lem-CSu-box-2 ∷ᵃ lem-CSu-box-2-at122441 ∷ᵃ lem-CSu-box-2-at243243 ∷ᵃ lem-CXbc-box ∷ᵃ lem-CXbc-box-at0214203143 ∷ᵃ lem-CXbc-box-at0330 ∷ᵃ lem-CXbc-box-at043043 ∷ᵃ lem-CXbc-box-at1221 ∷ᵃ lem-CXbc-box-at12243143 ∷ᵃ lem-CXbc-box-at13213442 ∷ᵃ lem-CXbc-box-at133441 ∷ᵃ lem-CXcb-box ∷ᵃ lem-CXcb-box-at0214203143 ∷ᵃ lem-CXcb-box-at0330 ∷ᵃ lem-CXcb-box-at043043 ∷ᵃ lem-CXcb-box-at1221 ∷ᵃ lem-CXcb-box-at12243143 ∷ᵃ lem-CXcb-box-at13213442 ∷ᵃ lem-CXcb-box-at133441 ∷ᵃ lem-QVQ-at021021 ∷ᵃ lem-QVQ-at03102132 ∷ᵃ lem-QVQ-at0410213243 ∷ᵃ lem-QVQ-at04203243 ∷ᵃ lem-QVQ-at13243142 ∷ᵃ lem-QVQ-at13243241 ∷ᵃ lem-QVQ-at14233142 ∷ᵃ lem-SWbc-box-at032032 ∷ᵃ lem-SWbc-box-at04203243 ∷ᵃ lem-SWbc-box-at13243142 ∷ᵃ lem-SWbc-box-at13243241 ∷ᵃ lem-SWbc-box-at14233142 ∷ᵃ lem-Sdu-box ∷ᵃ lem-Su-box ∷ᵃ lem-Su-box-at0210243143 ∷ᵃ lem-Su-box-at122441 ∷ᵃ lem-Su-box-at243243 ∷ᵃ lem-VPQ ∷ᵃ lem-VPQ-at0110 ∷ᵃ lem-VPQ-at0210243143 ∷ᵃ lem-VPQ-at0310243142 ∷ᵃ lem-VPQ-at0314203142 ∷ᵃ lem-VPQ-at0330 ∷ᵃ lem-VPQ-at043043 ∷ᵃ lem-VPQ-at1221 ∷ᵃ lem-VPQ-at122331 ∷ᵃ lem-VPQ-at122441 ∷ᵃ lem-VPQ-at132132 ∷ᵃ lem-VPQ-at13213442 ∷ᵃ lem-VPQ-at1331 ∷ᵃ lem-VPQ-at2332 ∷ᵃ lem-VPQ-at243243 ∷ᵃ lem-VPQ-at3443 ∷ᵃ lem-CSu-box-2-at0210243143 ∷ᵃ lem-CXbc-box-at0210243143 ∷ᵃ lem-CXbc-box-at0213213440 ∷ᵃ lem-CXbc-box-at0214213043 ∷ᵃ lem-CXbc-box-at022330 ∷ᵃ lem-CXbc-box-at02233440 ∷ᵃ lem-CXbc-box-at022440 ∷ᵃ lem-CXbc-box-at0312213440 ∷ᵃ lem-CXbc-box-at0312243140 ∷ᵃ lem-CXbc-box-at0314203142 ∷ᵃ lem-CXbc-box-at0314213042 ∷ᵃ lem-CXbc-box-at122331 ∷ᵃ lem-CXbc-box-at12233441 ∷ᵃ lem-CXbc-box-at122441 ∷ᵃ lem-CXbc-box-at132132 ∷ᵃ lem-CXbc-box-at1331 ∷ᵃ lem-CXbc-box-at14213243 ∷ᵃ lem-CXbc-box-at1441 ∷ᵃ lem-CXbc-box-at2332 ∷ᵃ lem-CXbc-box-at243243 ∷ᵃ lem-CXcb-box-at0210243143 ∷ᵃ lem-CXcb-box-at0213213440 ∷ᵃ lem-CXcb-box-at0214213043 ∷ᵃ lem-CXcb-box-at022330 ∷ᵃ lem-CXcb-box-at02233440 ∷ᵃ lem-CXcb-box-at0312213440 ∷ᵃ lem-CXcb-box-at0312243140 ∷ᵃ lem-CXcb-box-at0314203142 ∷ᵃ lem-CXcb-box-at0314213042 ∷ᵃ lem-CXcb-box-at122331 ∷ᵃ lem-CXcb-box-at12233441 ∷ᵃ lem-CXcb-box-at122441 ∷ᵃ lem-CXcb-box-at132132 ∷ᵃ lem-CXcb-box-at1331 ∷ᵃ lem-CXcb-box-at14213243 ∷ᵃ lem-CXcb-box-at1441 ∷ᵃ lem-CXcb-box-at2332 ∷ᵃ lem-CXcb-box-at243243 ∷ᵃ lem-QVQ-at0210213443 ∷ᵃ lem-QVQ-at0213243140 ∷ᵃ lem-QVQ-at0220 ∷ᵃ lem-QVQ-at032032 ∷ᵃ lem-QVQ-at14233241 ∷ᵃ lem-SWbc-box-at0213243140 ∷ᵃ lem-SWbc-box-at0220 ∷ᵃ lem-SWbc-box-at03102132 ∷ᵃ lem-VPQ-at0210233441 ∷ᵃ lem-VPQ-at0213203441 ∷ᵃ lem-VPQ-at0214203143 ∷ᵃ lem-VPQ-at0214213043 ∷ᵃ lem-VPQ-at022330 ∷ᵃ lem-VPQ-at022440 ∷ᵃ lem-VPQ-at0312243140 ∷ᵃ lem-VPQ-at0314213042 ∷ᵃ lem-VPQ-at12213443 ∷ᵃ lem-VPQ-at12233441 ∷ᵃ lem-VPQ-at14213243 ∷ᵃ lem-VPQ-at143143 ∷ᵃ lem-VPQ-at233442 ∷ᵃ lem-CXbc-box-at0210233441 ∷ᵃ lem-CXbc-box-at02102441 ∷ᵃ lem-CXbc-box-at02142041 ∷ᵃ lem-CXbc-box-at0310243142 ∷ᵃ lem-CXbc-box-at0310243241 ∷ᵃ lem-CXbc-box-at031031 ∷ᵃ lem-CXbc-box-at03103441 ∷ᵃ lem-CXbc-box-at0312203441 ∷ᵃ lem-CXbc-box-at0312243041 ∷ᵃ lem-CXbc-box-at0314213240 ∷ᵃ lem-CXbc-box-at03143041 ∷ᵃ lem-CXbc-box-at03143140 ∷ᵃ lem-CXbc-box-at03243240 ∷ᵃ lem-CXbc-box-at033440 ∷ᵃ lem-CXbc-box-at12213443 ∷ᵃ lem-CXbc-box-at143143 ∷ᵃ lem-CXbc-box-at233442 ∷ᵃ lem-CXbc-box-at2442 ∷ᵃ lem-CXbc-box-at3443 ∷ᵃ lem-CXcb-box-at0210233441 ∷ᵃ lem-CXcb-box-at02102441 ∷ᵃ lem-CXcb-box-at022440 ∷ᵃ lem-CXcb-box-at0310243142 ∷ᵃ lem-CXcb-box-at0310243241 ∷ᵃ lem-CXcb-box-at031031 ∷ᵃ lem-CXcb-box-at03103441 ∷ᵃ lem-CXcb-box-at0312203441 ∷ᵃ lem-CXcb-box-at0312243041 ∷ᵃ lem-CXcb-box-at0314213240 ∷ᵃ lem-CXcb-box-at03143041 ∷ᵃ lem-CXcb-box-at03143140 ∷ᵃ lem-CXcb-box-at03243240 ∷ᵃ lem-CXcb-box-at033440 ∷ᵃ lem-CXcb-box-at12213443 ∷ᵃ lem-CXcb-box-at143143 ∷ᵃ lem-CXcb-box-at233442 ∷ᵃ lem-CXcb-box-at2442 ∷ᵃ lem-CXcb-box-at3443 ∷ᵃ lem-SWbc-box-at0310213442 ∷ᵃ lem-SWbc-box-at14233241 ∷ᵃ lem-VPQ-at02102441 ∷ᵃ lem-VPQ-at02233440 ∷ᵃ lem-VPQ-at0310243241 ∷ᵃ lem-VPQ-at031031 ∷ᵃ lem-VPQ-at03103441 ∷ᵃ lem-VPQ-at0312203441 ∷ᵃ lem-VPQ-at0312243041 ∷ᵃ lem-VPQ-at0314213240 ∷ᵃ lem-VPQ-at03143140 ∷ᵃ lem-VPQ-at03243240 ∷ᵃ lem-VPQ-at033440 ∷ᵃ lem-VPQ-at12243143 ∷ᵃ lem-VPQ-at1441 ∷ᵃ lem-VPQ-at2442 ∷ᵃ lem-CXcb-box-at02142041 ∷ᵃ nil
lem-QVQ : _
lem-QVQ = D014.lem-QVQ sD014
lem-QVQ-at0210243143 : _
lem-QVQ-at0210243143 = D014.lem-QVQ-at0210243143 sD014
lem-QVQ-at243243 : _
lem-QVQ-at243243 = D014.lem-QVQ-at243243 sD014
lem-QVQ-at122441 : _
lem-QVQ-at122441 = D014.lem-QVQ-at122441 sD014
lem-SWbc-box : _
lem-SWbc-box = D014.lem-SWbc-box sD014
lem-SWbc-box-at1221 : _
lem-SWbc-box-at1221 = D014.lem-SWbc-box-at1221 sD014
lem-QVQ-at1221 : _
lem-QVQ-at1221 = D014.lem-QVQ-at1221 sD014
lem-QVQ-at2332 : _
lem-QVQ-at2332 = D014.lem-QVQ-at2332 sD014
lem-sym-bc-at13243142 : _
lem-sym-bc-at13243142 = D014.lem-sym-bc-at13243142 sD014
lem-QVQ-at122331 : _
lem-QVQ-at122331 = D014.lem-QVQ-at122331 sD014
lem-sym-bc-at13243241 : _
lem-sym-bc-at13243241 = D014.lem-sym-bc-at13243241 sD014
lem-QVQ-at132132 : _
lem-QVQ-at132132 = D014.lem-QVQ-at132132 sD014
lem-SWbc-box-at12243143 : _
lem-SWbc-box-at12243143 = D014.lem-SWbc-box-at12243143 sD014
lem-sym-bc-at14233142 : _
lem-sym-bc-at14233142 = D014.lem-sym-bc-at14233142 sD014
lem-box-cP-at14233142 : _
lem-box-cP-at14233142 = D014.lem-box-cP-at14233142 sD014
lem-QVQ-at13213442 : _
lem-QVQ-at13213442 = D014.lem-QVQ-at13213442 sD014
lem-QVQ-at1331 : _
lem-QVQ-at1331 = D014.lem-QVQ-at1331 sD014
lem-QVQ-at0110 : _
lem-QVQ-at0110 = D014.lem-QVQ-at0110 sD014
lem-SWbc-box-at133441 : _
lem-SWbc-box-at133441 = D014.lem-SWbc-box-at133441 sD014
lem-box-cP-at13243241 : _
lem-box-cP-at13243241 = D014.lem-box-cP-at13243241 sD014
lem-box-cP-at021021 : _
lem-box-cP-at021021 = D014.lem-box-cP-at021021 sD014
lem-SWbc-box-at13213442 : _
lem-SWbc-box-at13213442 = D014.lem-SWbc-box-at13213442 sD014
lem-box-cP-at13243142 : _
lem-box-cP-at13243142 = D014.lem-box-cP-at13243142 sD014
lem-box-cP-at03102132 : _
lem-box-cP-at03102132 = D014.lem-box-cP-at03102132 sD014
lem-QVQ-at3443 : _
lem-QVQ-at3443 = D014.lem-QVQ-at3443 sD014
lem-box-cP-at0410213243 : _
lem-box-cP-at0410213243 = D014.lem-box-cP-at0410213243 sD014
lem-QVQ-at043043 : _
lem-QVQ-at043043 = D014.lem-QVQ-at043043 sD014
lem-SWbc-box-at043043 : _
lem-SWbc-box-at043043 = D014.lem-SWbc-box-at043043 sD014
lem-QVQ-at0330 : _
lem-QVQ-at0330 = D014.lem-QVQ-at0330 sD014
lem-QVQ-at0314203142 : _
lem-QVQ-at0314203142 = D014.lem-QVQ-at0314203142 sD014
lem-QVQ-at0310243142 : _
lem-QVQ-at0310243142 = D014.lem-QVQ-at0310243142 sD014
lem-sym-bc-at04203243 : _
lem-sym-bc-at04203243 = D014.lem-sym-bc-at04203243 sD014
lem-sym-bc-at032032 : _
lem-sym-bc-at032032 = D014.lem-sym-bc-at032032 sD014
lem-SWbc-box-at0330 : _
lem-SWbc-box-at0330 = D014.lem-SWbc-box-at0330 sD014
lem-XCSX-box-2-at243243 : _
lem-XCSX-box-2-at243243 = D014.lem-XCSX-box-2-at243243 sD014
lem-XCSX-box-2-at122441 : _
lem-XCSX-box-2-at122441 = D014.lem-XCSX-box-2-at122441 sD014
lem-XCSX-box-2-at0210243143 : _
lem-XCSX-box-2-at0210243143 = D014.lem-XCSX-box-2-at0210243143 sD014
lem-SWbc-box-at0214203143 : _
lem-SWbc-box-at0214203143 = D014.lem-SWbc-box-at0214203143 sD014
lem-QVQ-at0214213043 : _
lem-QVQ-at0214213043 = D014.lem-QVQ-at0214213043 sD014
lem-QVQ-at0210233441 : _
lem-QVQ-at0210233441 = D014.lem-QVQ-at0210233441 sD014
lem-SWbc-box-at122441 : _
lem-SWbc-box-at122441 = D014.lem-SWbc-box-at122441 sD014
lem-QVQ-at12233441 : _
lem-QVQ-at12233441 = D014.lem-QVQ-at12233441 sD014
lem-SWbc-box-at14213243 : _
lem-SWbc-box-at14213243 = D014.lem-SWbc-box-at14213243 sD014
lem-QVQ-at143143 : _
lem-QVQ-at143143 = D014.lem-QVQ-at143143 sD014
lem-QVQ-at233442 : _
lem-QVQ-at233442 = D014.lem-QVQ-at233442 sD014
lem-SWbc-box-at0210243143 : _
lem-SWbc-box-at0210243143 = D014.lem-SWbc-box-at0210243143 sD014
lem-box-cP-at0210213443 : _
lem-box-cP-at0210213443 = D014.lem-box-cP-at0210213443 sD014
lem-SWbc-box-at243243 : _
lem-SWbc-box-at243243 = D014.lem-SWbc-box-at243243 sD014
lem-SWbc-box-at1441 : _
lem-SWbc-box-at1441 = D014.lem-SWbc-box-at1441 sD014
lem-box-cP-at14233241 : _
lem-box-cP-at14233241 = D014.lem-box-cP-at14233241 sD014
lem-QVQ-at12213443 : _
lem-QVQ-at12213443 = D014.lem-QVQ-at12213443 sD014
lem-SWbc-box-at0314213042 : _
lem-SWbc-box-at0314213042 = D014.lem-SWbc-box-at0314213042 sD014
lem-QVQ-at0213203441 : _
lem-QVQ-at0213203441 = D014.lem-QVQ-at0213203441 sD014
lem-SWbc-box-at0314203142 : _
lem-SWbc-box-at0314203142 = D014.lem-SWbc-box-at0314203142 sD014
lem-QVQ-at0314213042 : _
lem-QVQ-at0314213042 = D014.lem-QVQ-at0314213042 sD014
lem-SWbc-box-at0214213043 : _
lem-SWbc-box-at0214213043 = D014.lem-SWbc-box-at0214213043 sD014
lem-SWbc-box-at1331 : _
lem-SWbc-box-at1331 = D014.lem-SWbc-box-at1331 sD014
lem-box-cP-at032032 : _
lem-box-cP-at032032 = D014.lem-box-cP-at032032 sD014
lem-SWbc-box-at0312243140 : _
lem-SWbc-box-at0312243140 = D014.lem-SWbc-box-at0312243140 sD014
lem-SWbc-box-at0312213440 : _
lem-SWbc-box-at0312213440 = D014.lem-SWbc-box-at0312213440 sD014
lem-QVQ-at0312243140 : _
lem-QVQ-at0312243140 = D014.lem-QVQ-at0312243140 sD014
lem-SWbc-box-at132132 : _
lem-SWbc-box-at132132 = D014.lem-SWbc-box-at132132 sD014
lem-SWbc-box-at022330 : _
lem-SWbc-box-at022330 = D014.lem-SWbc-box-at022330 sD014
lem-box-cP-at0220 : _
lem-box-cP-at0220 = D014.lem-box-cP-at0220 sD014
lem-sym-bc-at0213243140 : _
lem-sym-bc-at0213243140 = D014.lem-sym-bc-at0213243140 sD014
lem-SWbc-box-at0213213440 : _
lem-SWbc-box-at0213213440 = D014.lem-SWbc-box-at0213213440 sD014
lem-box-cP-at0213243140 : _
lem-box-cP-at0213243140 = D014.lem-box-cP-at0213243140 sD014
lem-sym-bc-at0220 : _
lem-sym-bc-at0220 = D014.lem-sym-bc-at0220 sD014
lem-QVQ-at022330 : _
lem-QVQ-at022330 = D014.lem-QVQ-at022330 sD014
lem-SWbc-box-at122331 : _
lem-SWbc-box-at122331 = D014.lem-SWbc-box-at122331 sD014
lem-QVQ-at14213243 : _
lem-QVQ-at14213243 = D014.lem-QVQ-at14213243 sD014
lem-SWbc-box-at12233441 : _
lem-SWbc-box-at12233441 = D014.lem-SWbc-box-at12233441 sD014
lem-SWbc-box-at2332 : _
lem-SWbc-box-at2332 = D014.lem-SWbc-box-at2332 sD014
lem-sym-bc-at03102132 : _
lem-sym-bc-at03102132 = D014.lem-sym-bc-at03102132 sD014
lem-QVQ-at0214203143 : _
lem-QVQ-at0214203143 = D014.lem-QVQ-at0214203143 sD014
lem-SWbc-box-at02233440 : _
lem-SWbc-box-at02233440 = D014.lem-SWbc-box-at02233440 sD014
lem-QVQ-at022440 : _
lem-QVQ-at022440 = D014.lem-QVQ-at022440 sD014
lem-SWbc-box-at022440 : _
lem-SWbc-box-at022440 = D014.lem-SWbc-box-at022440 sD014
lem-QVQ-at02233440 : _
lem-QVQ-at02233440 = D014.lem-QVQ-at02233440 sD014
lem-QVQ-at1441 : _
lem-QVQ-at1441 = D014.lem-QVQ-at1441 sD014
lem-SWbc-box-at0210233441 : _
lem-SWbc-box-at0210233441 = D014.lem-SWbc-box-at0210233441 sD014
lem-QVQ-at02102441 : _
lem-QVQ-at02102441 = D014.lem-QVQ-at02102441 sD014
lem-SWbc-box-at02102441 : _
lem-SWbc-box-at02102441 = D014.lem-SWbc-box-at02102441 sD014
lem-SWbc-box-at233442 : _
lem-SWbc-box-at233442 = D014.lem-SWbc-box-at233442 sD014
lem-QVQ-at2442 : _
lem-QVQ-at2442 = D014.lem-QVQ-at2442 sD014
lem-SWbc-box-at2442 : _
lem-SWbc-box-at2442 = D014.lem-SWbc-box-at2442 sD014
lem-SWbc-box-at143143 : _
lem-SWbc-box-at143143 = D014.lem-SWbc-box-at143143 sD014
lem-SWbc-box-at12213443 : _
lem-SWbc-box-at12213443 = D014.lem-SWbc-box-at12213443 sD014
lem-QVQ-at12243143 : _
lem-QVQ-at12243143 = D014.lem-QVQ-at12243143 sD014
lem-SWbc-box-at03143140 : _
lem-SWbc-box-at03143140 = D014.lem-SWbc-box-at03143140 sD014
lem-QVQ-at0314213240 : _
lem-QVQ-at0314213240 = D014.lem-QVQ-at0314213240 sD014
lem-SWbc-box-at0314213240 : _
lem-SWbc-box-at0314213240 = D014.lem-SWbc-box-at0314213240 sD014
lem-QVQ-at03143140 : _
lem-QVQ-at03143140 = D014.lem-QVQ-at03143140 sD014
lem-QVQ-at03243240 : _
lem-QVQ-at03243240 = D014.lem-QVQ-at03243240 sD014
lem-SWbc-box-at033440 : _
lem-SWbc-box-at033440 = D014.lem-SWbc-box-at033440 sD014
lem-SWbc-box-at03243240 : _
lem-SWbc-box-at03243240 = D014.lem-SWbc-box-at03243240 sD014
lem-QVQ-at033440 : _
lem-QVQ-at033440 = D014.lem-QVQ-at033440 sD014
lem-SWbc-box-at03103441 : _
lem-SWbc-box-at03103441 = D014.lem-SWbc-box-at03103441 sD014
lem-QVQ-at0310243241 : _
lem-QVQ-at0310243241 = D014.lem-QVQ-at0310243241 sD014
lem-SWbc-box-at0310243241 : _
lem-SWbc-box-at0310243241 = D014.lem-SWbc-box-at0310243241 sD014
lem-QVQ-at03103441 : _
lem-QVQ-at03103441 = D014.lem-QVQ-at03103441 sD014
lem-SWbc-box-at0310243142 : _
lem-SWbc-box-at0310243142 = D014.lem-SWbc-box-at0310243142 sD014
lem-sym-bc-at0310213442 : _
lem-sym-bc-at0310213442 = D014.lem-sym-bc-at0310213442 sD014
lem-SWbc-box-at0312203441 : _
lem-SWbc-box-at0312203441 = D014.lem-SWbc-box-at0312203441 sD014
lem-QVQ-at0312243041 : _
lem-QVQ-at0312243041 = D014.lem-QVQ-at0312243041 sD014
lem-SWbc-box-at0312243041 : _
lem-SWbc-box-at0312243041 = D014.lem-SWbc-box-at0312243041 sD014
lem-QVQ-at0312203441 : _
lem-QVQ-at0312203441 = D014.lem-QVQ-at0312203441 sD014
lem-SWbc-box-at3443 : _
lem-SWbc-box-at3443 = D014.lem-SWbc-box-at3443 sD014
lem-SWbc-box-at031031 : _
lem-SWbc-box-at031031 = D014.lem-SWbc-box-at031031 sD014
lem-QVQ-at031031 : _
lem-QVQ-at031031 = D014.lem-QVQ-at031031 sD014
lem-SWbc-box-at03143041 : _
lem-SWbc-box-at03143041 = D014.lem-SWbc-box-at03143041 sD014
lem-SWbc-box-at02142041 : _
lem-SWbc-box-at02142041 = D014.lem-SWbc-box-at02142041 sD014
sD013 : SD013
sD013 = (λ c → lem-comm-CS03-TOFF412 (lit c)) ∷ᵃ (λ c → lem-comm-CSd03-TOFF412 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-TOFF403 (lit c)) ∷ᵃ (λ c → lem-comm-CX21-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CX23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX31-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX32-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CZ03-TOFF412 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF412-CSd03 (lit c)) ∷ᵃ (λ c → lem-comm-CS02-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-CS04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CSd02-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-TOFF401 (lit c)) ∷ᵃ (λ c → lem-comm-CZ03-TOFF214 (lit c)) ∷ᵃ (λ c → lem-comm-CZ12-TOFF403 (lit c)) ∷ᵃ (λ c → lem-comm-CZ14-TOFF203 (lit c)) ∷ᵃ (λ c → lem-comm-CZ14-TOFF302 (lit c)) ∷ᵃ (λ c → lem-comm-CSd02-TOFF413 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-TOFF402 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF413-CSd02 (lit c)) ∷ᵃ (λ c → lem-comm-CS02-TOFF413 (lit c)) ∷ᵃ (λ c → lem-comm-CZ02-TOFF413 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF403-CSd12 (lit c)) ∷ᵃ lem-box-tQ-at0214203143 ∷ᵃ lem-box-tQ-at043043 ∷ᵃ lem-tP-at043043 ∷ᵃ lem-box-tQ-at02132031 ∷ᵃ lem-box-tQ-at022440 ∷ᵃ lem-box-tQ-at03122031 ∷ᵃ lem-box-tQ-at04122041 ∷ᵃ lem-tP-at02132031 ∷ᵃ lem-tP-at022440 ∷ᵃ lem-tP-at03122031 ∷ᵃ lem-tP-at04122041 ∷ᵃ lem-CSdu-box-2-at04203243 ∷ᵃ lem-Su-box-at04203243 ∷ᵃ lem-box-tQ-at0410233142 ∷ᵃ lem-box-tQ-at04122140 ∷ᵃ lem-box-tQ-at0412233140 ∷ᵃ lem-box-tQ-at0413203241 ∷ᵃ lem-box-tQ-at0413213240 ∷ᵃ lem-box-tQ-at04133140 ∷ᵃ lem-tP-at0410233142 ∷ᵃ lem-tP-at04122140 ∷ᵃ lem-tP-at0412233140 ∷ᵃ lem-tP-at0413203241 ∷ᵃ lem-tP-at0413213240 ∷ᵃ lem-tP-at0440 ∷ᵃ nil
lem-VPQ-at0413213240 : _
lem-VPQ-at0413213240 = D013.lem-VPQ-at0413213240 sD013
lem-CXbc-box-at0412233140 : _
lem-CXbc-box-at0412233140 = D013.lem-CXbc-box-at0412233140 sD013
lem-CXcb-box-at0412233140 : _
lem-CXcb-box-at0412233140 = D013.lem-CXcb-box-at0412233140 sD013
lem-VPQ-at0410233142 : _
lem-VPQ-at0410233142 = D013.lem-VPQ-at0410233142 sD013
lem-CXbc-box-at04122140 : _
lem-CXbc-box-at04122140 = D013.lem-CXbc-box-at04122140 sD013
lem-CXcb-box-at04122140 : _
lem-CXcb-box-at04122140 = D013.lem-CXcb-box-at04122140 sD013
lem-VPQ-at0412233140 : _
lem-VPQ-at0412233140 = D013.lem-VPQ-at0412233140 sD013
lem-CSdu-box-2-at04122041 : _
lem-CSdu-box-2-at04122041 = D013.lem-CSdu-box-2-at04122041 sD013
lem-Su-box-at04122041 : _
lem-Su-box-at04122041 = D013.lem-Su-box-at04122041 sD013
lem-VPQ-at0413203241 : _
lem-VPQ-at0413203241 = D013.lem-VPQ-at0413203241 sD013
lem-VPQ-at04122140 : _
lem-VPQ-at04122140 = D013.lem-VPQ-at04122140 sD013
lem-XCSX-box-2-at04203243 : _
lem-XCSX-box-2-at04203243 = D013.lem-XCSX-box-2-at04203243 sD013
lem-CXbc-box-at04133140 : _
lem-CXbc-box-at04133140 = D013.lem-CXbc-box-at04133140 sD013
lem-CXcb-box-at04133140 : _
lem-CXcb-box-at04133140 = D013.lem-CXcb-box-at04133140 sD013
lem-CXbc-box-at0413213240 : _
lem-CXbc-box-at0413213240 = D013.lem-CXbc-box-at0413213240 sD013
lem-CXcb-box-at0413213240 : _
lem-CXcb-box-at0413213240 = D013.lem-CXcb-box-at0413213240 sD013
sD015 : SD015
sD015 = lem-nat-SWbc-at021021 ∷ᵃ lem-nat-SWbc-at0210213443 ∷ᵃ lem-nat-SWbc-at0410213243 ∷ᵃ lem-tP-at0213243041 ∷ᵃ lem-tP-at0214233041 ∷ᵃ lem-tP-at0310213442 ∷ᵃ lem-nat-SWbc-at0214233041 ∷ᵃ lem-CXbc-box-at02102331 ∷ᵃ lem-CXbc-box-at02132031 ∷ᵃ lem-CXbc-box-at02132130 ∷ᵃ lem-CXbc-box-at03122031 ∷ᵃ lem-CXbc-box-at03122130 ∷ᵃ lem-CXbc-box-at0314203241 ∷ᵃ lem-CXbc-box-at041041 ∷ᵃ lem-CXbc-box-at04122041 ∷ᵃ lem-CXbc-box-at0412233041 ∷ᵃ lem-CXbc-box-at0413203142 ∷ᵃ lem-CXbc-box-at0413213042 ∷ᵃ lem-CXbc-box-at04233240 ∷ᵃ lem-CXbc-box-at0440 ∷ᵃ lem-CXbc-box-at142142 ∷ᵃ lem-CXcb-box-at02102331 ∷ᵃ lem-CXcb-box-at02132031 ∷ᵃ lem-CXcb-box-at02132130 ∷ᵃ lem-CXcb-box-at03122031 ∷ᵃ lem-CXcb-box-at03122130 ∷ᵃ lem-CXcb-box-at0314203241 ∷ᵃ lem-CXcb-box-at041041 ∷ᵃ lem-CXcb-box-at04122041 ∷ᵃ lem-CXcb-box-at0412233041 ∷ᵃ lem-CXcb-box-at0413203142 ∷ᵃ lem-CXcb-box-at0413213042 ∷ᵃ lem-CXcb-box-at04233240 ∷ᵃ lem-CXcb-box-at0440 ∷ᵃ lem-CXcb-box-at142142 ∷ᵃ lem-QVQ-at0213243041 ∷ᵃ lem-QVQ-at0214233041 ∷ᵃ lem-QVQ-at0310213442 ∷ᵃ lem-SWbc-box-at021021 ∷ᵃ lem-SWbc-box-at0210213443 ∷ᵃ lem-SWbc-box-at0214233041 ∷ᵃ lem-SWbc-box-at0410213243 ∷ᵃ lem-VPQ-at02102331 ∷ᵃ lem-VPQ-at02132031 ∷ᵃ lem-VPQ-at02132130 ∷ᵃ lem-VPQ-at02142041 ∷ᵃ lem-VPQ-at02142140 ∷ᵃ lem-VPQ-at03122031 ∷ᵃ lem-VPQ-at03122130 ∷ᵃ lem-VPQ-at0314203241 ∷ᵃ lem-VPQ-at03143041 ∷ᵃ lem-VPQ-at03243042 ∷ᵃ lem-VPQ-at0410233241 ∷ᵃ lem-VPQ-at04103143 ∷ᵃ lem-VPQ-at04122041 ∷ᵃ lem-VPQ-at0412213043 ∷ᵃ lem-VPQ-at0412233041 ∷ᵃ lem-VPQ-at0413203142 ∷ᵃ lem-VPQ-at04233042 ∷ᵃ lem-VPQ-at0440 ∷ᵃ lem-VPQ-at142142 ∷ᵃ lem-CSdu-box-2-at04122041 ∷ᵃ lem-CXbc-box-at04122140 ∷ᵃ lem-CXbc-box-at0412233140 ∷ᵃ lem-CXbc-box-at0413213240 ∷ᵃ lem-CXbc-box-at04133140 ∷ᵃ lem-CXcb-box-at04122140 ∷ᵃ lem-CXcb-box-at0412233140 ∷ᵃ lem-CXcb-box-at0413213240 ∷ᵃ lem-CXcb-box-at04133140 ∷ᵃ lem-Su-box-at04122041 ∷ᵃ lem-VPQ-at0410233142 ∷ᵃ lem-VPQ-at04122140 ∷ᵃ lem-VPQ-at0412233140 ∷ᵃ lem-VPQ-at0413203241 ∷ᵃ lem-VPQ-at0413213240 ∷ᵃ lem-XCSX-box-2-at04203243 ∷ᵃ nil
lem-box-cP-at0214233041 : _
lem-box-cP-at0214233041 = D015.lem-box-cP-at0214233041 sD015
lem-SWbc-box-at0314203241 : _
lem-SWbc-box-at0314203241 = D015.lem-SWbc-box-at0314203241 sD015
lem-sym-bc-at0214233041 : _
lem-sym-bc-at0214233041 = D015.lem-sym-bc-at0214233041 sD015
lem-SWbc-box-at02132130 : _
lem-SWbc-box-at02132130 = D015.lem-SWbc-box-at02132130 sD015
lem-QVQ-at03143041 : _
lem-QVQ-at03143041 = D015.lem-QVQ-at03143041 sD015
lem-QVQ-at02132031 : _
lem-QVQ-at02132031 = D015.lem-QVQ-at02132031 sD015
lem-box-cP-at0310213442 : _
lem-box-cP-at0310213442 = D015.lem-box-cP-at0310213442 sD015
lem-SWbc-box-at02132031 : _
lem-SWbc-box-at02132031 = D015.lem-SWbc-box-at02132031 sD015
lem-QVQ-at02132130 : _
lem-QVQ-at02132130 = D015.lem-QVQ-at02132130 sD015
lem-box-cP-at0213243041 : _
lem-box-cP-at0213243041 = D015.lem-box-cP-at0213243041 sD015
lem-SWbc-box-at03122130 : _
lem-SWbc-box-at03122130 = D015.lem-SWbc-box-at03122130 sD015
lem-QVQ-at03122031 : _
lem-QVQ-at03122031 = D015.lem-QVQ-at03122031 sD015
lem-SWbc-box-at03122031 : _
lem-SWbc-box-at03122031 = D015.lem-SWbc-box-at03122031 sD015
lem-QVQ-at03122130 : _
lem-QVQ-at03122130 = D015.lem-QVQ-at03122130 sD015
sD016 : SD016
sD016 = (λ c → lem-comm-CS12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CS23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX12-CCZ034 (lit c)) ∷ᵃ lem-nat-SWbc-at0214203143 ∷ᵃ lem-nat-SWbc-at0214213043 ∷ᵃ lem-nat-SWbc-at0314203142 ∷ᵃ lem-nat-SWbc-at0314213042 ∷ᵃ lem-nat-SWbc-at122441 ∷ᵃ lem-nat-SWbc-at132132 ∷ᵃ lem-nat-SWbc-at1331 ∷ᵃ lem-nat-SWbc-at14213243 ∷ᵃ lem-sym-ab-at03102132 ∷ᵃ lem-sym-ab-at0410213243 ∷ᵃ lem-nat-SWbc-at0210233441 ∷ᵃ lem-nat-SWbc-at02102441 ∷ᵃ lem-nat-SWbc-at02132031 ∷ᵃ lem-nat-SWbc-at02132130 ∷ᵃ lem-nat-SWbc-at02233440 ∷ᵃ lem-nat-SWbc-at022440 ∷ᵃ lem-nat-SWbc-at0310243241 ∷ᵃ lem-nat-SWbc-at03103441 ∷ᵃ lem-nat-SWbc-at03122031 ∷ᵃ lem-nat-SWbc-at03122130 ∷ᵃ lem-nat-SWbc-at03243240 ∷ᵃ lem-nat-SWbc-at033440 ∷ᵃ lem-nat-SWbc-at12233441 ∷ᵃ lem-nat-SWbc-at143143 ∷ᵃ lem-nat-SWbc-at233442 ∷ᵃ lem-nat-SWbc-at2442 ∷ᵃ lem-sym-ab-at0213243041 ∷ᵃ lem-box-tQ-at0210213443 ∷ᵃ lem-box-tQ-at0213243140 ∷ᵃ lem-box-tQ-at0220 ∷ᵃ lem-nat-SWbc ∷ᵃ lem-nat-SWbc-at0210243143 ∷ᵃ lem-nat-SWbc-at0213213440 ∷ᵃ lem-nat-SWbc-at0312213440 ∷ᵃ lem-nat-SWbc-at0312243140 ∷ᵃ lem-nat-SWbc-at0330 ∷ᵃ lem-nat-SWbc-at043043 ∷ᵃ lem-nat-SWbc-at1221 ∷ᵃ lem-nat-SWbc-at122331 ∷ᵃ lem-nat-SWbc-at12243143 ∷ᵃ lem-nat-SWbc-at13213442 ∷ᵃ lem-nat-SWbc-at133441 ∷ᵃ lem-nat-SWbc-at1441 ∷ᵃ lem-nat-SWbc-at2332 ∷ᵃ lem-nat-SWbc-at243243 ∷ᵃ lem-box-tQ-at021021 ∷ᵃ lem-box-tQ-at0213243041 ∷ᵃ lem-box-tQ-at0214233041 ∷ᵃ lem-nat-SWbc-at0310243142 ∷ᵃ lem-nat-SWbc-at031031 ∷ᵃ lem-nat-SWbc-at0312203441 ∷ᵃ lem-nat-SWbc-at0312243041 ∷ᵃ lem-nat-SWbc-at0314203241 ∷ᵃ lem-nat-SWbc-at0314213240 ∷ᵃ lem-nat-SWbc-at03143041 ∷ᵃ lem-nat-SWbc-at03143140 ∷ᵃ lem-nat-SWbc-at12213443 ∷ᵃ lem-nat-SWbc-at3443 ∷ᵃ lem-P-box-at0220 ∷ᵃ lem-P-box-at032032 ∷ᵃ lem-P-box-at13243142 ∷ᵃ lem-P-box-at13243241 ∷ᵃ lem-P-box-at14233142 ∷ᵃ lem-P-box-at14233241 ∷ᵃ lem-box-tQ ∷ᵃ lem-box-tQ-at0312243140 ∷ᵃ lem-box-tQ-at1221 ∷ᵃ lem-box-tQ-at12213443 ∷ᵃ lem-box-tQ-at3443 ∷ᵃ lem-nat-SWbc-at022330 ∷ᵃ lem-tP ∷ᵃ lem-tP-at0110 ∷ᵃ lem-tP-at0210233441 ∷ᵃ lem-tP-at0210243143 ∷ᵃ lem-tP-at0213203441 ∷ᵃ lem-tP-at0214213043 ∷ᵃ lem-tP-at0310243142 ∷ᵃ lem-tP-at0312243140 ∷ᵃ lem-tP-at0314203142 ∷ᵃ lem-tP-at0314213042 ∷ᵃ lem-tP-at0330 ∷ᵃ lem-tP-at043043 ∷ᵃ lem-tP-at1221 ∷ᵃ lem-tP-at12213443 ∷ᵃ lem-tP-at122331 ∷ᵃ lem-tP-at12233441 ∷ᵃ lem-tP-at122441 ∷ᵃ lem-tP-at132132 ∷ᵃ lem-tP-at13213442 ∷ᵃ lem-tP-at1331 ∷ᵃ lem-tP-at143143 ∷ᵃ lem-tP-at2332 ∷ᵃ lem-tP-at233442 ∷ᵃ lem-tP-at243243 ∷ᵃ lem-tP-at3443 ∷ᵃ lem-P-box-at021021 ∷ᵃ lem-P-box-at0210213443 ∷ᵃ lem-P-box-at0213243041 ∷ᵃ lem-P-box-at0213243140 ∷ᵃ lem-P-box-at0214233041 ∷ᵃ lem-P-box-at03102132 ∷ᵃ lem-P-box-at0310213442 ∷ᵃ lem-box-tQ-at0312243041 ∷ᵃ lem-box-tQ-at03143041 ∷ᵃ lem-nat-SWbc-at02142041 ∷ᵃ lem-tP-at02102441 ∷ᵃ lem-tP-at02132031 ∷ᵃ lem-tP-at02132130 ∷ᵃ lem-tP-at0214203143 ∷ᵃ lem-tP-at022330 ∷ᵃ lem-tP-at02233440 ∷ᵃ lem-tP-at022440 ∷ᵃ lem-tP-at0310243241 ∷ᵃ lem-tP-at031031 ∷ᵃ lem-tP-at03103441 ∷ᵃ lem-tP-at03122031 ∷ᵃ lem-tP-at0312203441 ∷ᵃ lem-tP-at03122130 ∷ᵃ lem-tP-at0312243041 ∷ᵃ lem-tP-at0314213240 ∷ᵃ lem-tP-at03143041 ∷ᵃ lem-tP-at03143140 ∷ᵃ lem-tP-at03243240 ∷ᵃ lem-tP-at033440 ∷ᵃ lem-tP-at12243143 ∷ᵃ lem-tP-at14213243 ∷ᵃ lem-tP-at1441 ∷ᵃ lem-tP-at2442 ∷ᵃ lem-QVQ ∷ᵃ lem-QVQ-at0110 ∷ᵃ lem-QVQ-at0210233441 ∷ᵃ lem-QVQ-at0210243143 ∷ᵃ lem-QVQ-at02102441 ∷ᵃ lem-QVQ-at0213203441 ∷ᵃ lem-QVQ-at0214203143 ∷ᵃ lem-QVQ-at0214213043 ∷ᵃ lem-QVQ-at022330 ∷ᵃ lem-QVQ-at02233440 ∷ᵃ lem-QVQ-at022440 ∷ᵃ lem-QVQ-at0310243142 ∷ᵃ lem-QVQ-at0310243241 ∷ᵃ lem-QVQ-at031031 ∷ᵃ lem-QVQ-at03103441 ∷ᵃ lem-QVQ-at0312203441 ∷ᵃ lem-QVQ-at0312243041 ∷ᵃ lem-QVQ-at0312243140 ∷ᵃ lem-QVQ-at0314203142 ∷ᵃ lem-QVQ-at0314213042 ∷ᵃ lem-QVQ-at0314213240 ∷ᵃ lem-QVQ-at03143140 ∷ᵃ lem-QVQ-at03243240 ∷ᵃ lem-QVQ-at0330 ∷ᵃ lem-QVQ-at033440 ∷ᵃ lem-QVQ-at043043 ∷ᵃ lem-QVQ-at1221 ∷ᵃ lem-QVQ-at12213443 ∷ᵃ lem-QVQ-at122331 ∷ᵃ lem-QVQ-at12233441 ∷ᵃ lem-QVQ-at12243143 ∷ᵃ lem-QVQ-at122441 ∷ᵃ lem-QVQ-at132132 ∷ᵃ lem-QVQ-at13213442 ∷ᵃ lem-QVQ-at1331 ∷ᵃ lem-QVQ-at14213243 ∷ᵃ lem-QVQ-at143143 ∷ᵃ lem-QVQ-at1441 ∷ᵃ lem-QVQ-at2332 ∷ᵃ lem-QVQ-at233442 ∷ᵃ lem-QVQ-at243243 ∷ᵃ lem-QVQ-at2442 ∷ᵃ lem-QVQ-at3443 ∷ᵃ lem-SWbc-box ∷ᵃ lem-SWbc-box-at0210233441 ∷ᵃ lem-SWbc-box-at0210243143 ∷ᵃ lem-SWbc-box-at02102441 ∷ᵃ lem-SWbc-box-at0213213440 ∷ᵃ lem-SWbc-box-at0214203143 ∷ᵃ lem-SWbc-box-at02142041 ∷ᵃ lem-SWbc-box-at0214213043 ∷ᵃ lem-SWbc-box-at022330 ∷ᵃ lem-SWbc-box-at02233440 ∷ᵃ lem-SWbc-box-at022440 ∷ᵃ lem-SWbc-box-at0310243142 ∷ᵃ lem-SWbc-box-at0310243241 ∷ᵃ lem-SWbc-box-at031031 ∷ᵃ lem-SWbc-box-at03103441 ∷ᵃ lem-SWbc-box-at0312203441 ∷ᵃ lem-SWbc-box-at0312213440 ∷ᵃ lem-SWbc-box-at0312243041 ∷ᵃ lem-SWbc-box-at0312243140 ∷ᵃ lem-SWbc-box-at0314203142 ∷ᵃ lem-SWbc-box-at0314213042 ∷ᵃ lem-SWbc-box-at0314213240 ∷ᵃ lem-SWbc-box-at03143041 ∷ᵃ lem-SWbc-box-at03143140 ∷ᵃ lem-SWbc-box-at03243240 ∷ᵃ lem-SWbc-box-at0330 ∷ᵃ lem-SWbc-box-at033440 ∷ᵃ lem-SWbc-box-at043043 ∷ᵃ lem-SWbc-box-at1221 ∷ᵃ lem-SWbc-box-at12213443 ∷ᵃ lem-SWbc-box-at122331 ∷ᵃ lem-SWbc-box-at12233441 ∷ᵃ lem-SWbc-box-at12243143 ∷ᵃ lem-SWbc-box-at122441 ∷ᵃ lem-SWbc-box-at132132 ∷ᵃ lem-SWbc-box-at13213442 ∷ᵃ lem-SWbc-box-at1331 ∷ᵃ lem-SWbc-box-at133441 ∷ᵃ lem-SWbc-box-at14213243 ∷ᵃ lem-SWbc-box-at143143 ∷ᵃ lem-SWbc-box-at1441 ∷ᵃ lem-SWbc-box-at2332 ∷ᵃ lem-SWbc-box-at233442 ∷ᵃ lem-SWbc-box-at243243 ∷ᵃ lem-SWbc-box-at2442 ∷ᵃ lem-SWbc-box-at3443 ∷ᵃ lem-XCSX-box-2-at0210243143 ∷ᵃ lem-XCSX-box-2-at122441 ∷ᵃ lem-XCSX-box-2-at243243 ∷ᵃ lem-box-cP-at021021 ∷ᵃ lem-box-cP-at0210213443 ∷ᵃ lem-box-cP-at0213243140 ∷ᵃ lem-box-cP-at0220 ∷ᵃ lem-box-cP-at03102132 ∷ᵃ lem-box-cP-at032032 ∷ᵃ lem-box-cP-at0410213243 ∷ᵃ lem-box-cP-at13243142 ∷ᵃ lem-box-cP-at13243241 ∷ᵃ lem-box-cP-at14233142 ∷ᵃ lem-box-cP-at14233241 ∷ᵃ lem-sym-bc-at03102132 ∷ᵃ lem-sym-bc-at0310213442 ∷ᵃ lem-sym-bc-at032032 ∷ᵃ lem-sym-bc-at04203243 ∷ᵃ lem-sym-bc-at13243142 ∷ᵃ lem-QVQ-at02132031 ∷ᵃ lem-QVQ-at02132130 ∷ᵃ lem-QVQ-at03122031 ∷ᵃ lem-QVQ-at03122130 ∷ᵃ lem-QVQ-at03143041 ∷ᵃ lem-SWbc-box-at02132031 ∷ᵃ lem-SWbc-box-at02132130 ∷ᵃ lem-SWbc-box-at03122031 ∷ᵃ lem-SWbc-box-at03122130 ∷ᵃ lem-SWbc-box-at0314203241 ∷ᵃ lem-box-cP-at0213243041 ∷ᵃ lem-box-cP-at0214233041 ∷ᵃ lem-box-cP-at0310213442 ∷ᵃ lem-sym-bc-at0214233041 ∷ᵃ nil
lem-box-cP : _
lem-box-cP = D016.lem-box-cP sD016
lem-box-cP-at0210243143 : _
lem-box-cP-at0210243143 = D016.lem-box-cP-at0210243143 sD016
lem-box-cP-at243243 : _
lem-box-cP-at243243 = D016.lem-box-cP-at243243 sD016
lem-box-cP-at122441 : _
lem-box-cP-at122441 = D016.lem-box-cP-at122441 sD016
lem-sym-bc : _
lem-sym-bc = D016.lem-sym-bc sD016
lem-sym-bc-at1221 : _
lem-sym-bc-at1221 = D016.lem-sym-bc-at1221 sD016
lem-box-cP-at1221 : _
lem-box-cP-at1221 = D016.lem-box-cP-at1221 sD016
lem-box-cP-at2332 : _
lem-box-cP-at2332 = D016.lem-box-cP-at2332 sD016
lem-box-cP-at122331 : _
lem-box-cP-at122331 = D016.lem-box-cP-at122331 sD016
lem-box-cP-at132132 : _
lem-box-cP-at132132 = D016.lem-box-cP-at132132 sD016
lem-sym-bc-at12243143 : _
lem-sym-bc-at12243143 = D016.lem-sym-bc-at12243143 sD016
lem-pairs-at14233142 : _
lem-pairs-at14233142 = D016.lem-pairs-at14233142 sD016
lem-box-cP-at13213442 : _
lem-box-cP-at13213442 = D016.lem-box-cP-at13213442 sD016
lem-box-cP-at1331 : _
lem-box-cP-at1331 = D016.lem-box-cP-at1331 sD016
lem-sym-bc-at133441 : _
lem-sym-bc-at133441 = D016.lem-sym-bc-at133441 sD016
lem-pairs-at13243241 : _
lem-pairs-at13243241 = D016.lem-pairs-at13243241 sD016
lem-sym-bc-at13213442 : _
lem-sym-bc-at13213442 = D016.lem-sym-bc-at13213442 sD016
lem-pairs-at13243142 : _
lem-pairs-at13243142 = D016.lem-pairs-at13243142 sD016
lem-box-cP-at3443 : _
lem-box-cP-at3443 = D016.lem-box-cP-at3443 sD016
lem-box-cP-at043043 : _
lem-box-cP-at043043 = D016.lem-box-cP-at043043 sD016
lem-sym-bc-at043043 : _
lem-sym-bc-at043043 = D016.lem-sym-bc-at043043 sD016
lem-box-cP-at0330 : _
lem-box-cP-at0330 = D016.lem-box-cP-at0330 sD016
lem-box-cP-at0314203142 : _
lem-box-cP-at0314203142 = D016.lem-box-cP-at0314203142 sD016
lem-box-cP-at0310243142 : _
lem-box-cP-at0310243142 = D016.lem-box-cP-at0310243142 sD016
lem-sym-bc-at0330 : _
lem-sym-bc-at0330 = D016.lem-sym-bc-at0330 sD016
lem-CXu-box-4-at03102132 : _
lem-CXu-box-4-at03102132 = D016.lem-CXu-box-4-at03102132 sD016
lem-sym-bc-at0214203143 : _
lem-sym-bc-at0214203143 = D016.lem-sym-bc-at0214203143 sD016
lem-box-cP-at0214213043 : _
lem-box-cP-at0214213043 = D016.lem-box-cP-at0214213043 sD016
lem-box-cP-at0210233441 : _
lem-box-cP-at0210233441 = D016.lem-box-cP-at0210233441 sD016
lem-sym-bc-at122441 : _
lem-sym-bc-at122441 = D016.lem-sym-bc-at122441 sD016
lem-box-cP-at12233441 : _
lem-box-cP-at12233441 = D016.lem-box-cP-at12233441 sD016
lem-sym-bc-at14213243 : _
lem-sym-bc-at14213243 = D016.lem-sym-bc-at14213243 sD016
lem-box-cP-at143143 : _
lem-box-cP-at143143 = D016.lem-box-cP-at143143 sD016
lem-sym-bc-at0210243143 : _
lem-sym-bc-at0210243143 = D016.lem-sym-bc-at0210243143 sD016
lem-sym-bc-at243243 : _
lem-sym-bc-at243243 = D016.lem-sym-bc-at243243 sD016
lem-sym-bc-at1441 : _
lem-sym-bc-at1441 = D016.lem-sym-bc-at1441 sD016
lem-pairs-at14233241 : _
lem-pairs-at14233241 = D016.lem-pairs-at14233241 sD016
lem-box-cP-at12213443 : _
lem-box-cP-at12213443 = D016.lem-box-cP-at12213443 sD016
lem-sym-bc-at0314213042 : _
lem-sym-bc-at0314213042 = D016.lem-sym-bc-at0314213042 sD016
lem-box-cP-at0213203441 : _
lem-box-cP-at0213203441 = D016.lem-box-cP-at0213203441 sD016
lem-sym-bc-at0314203142 : _
lem-sym-bc-at0314203142 = D016.lem-sym-bc-at0314203142 sD016
lem-box-cP-at0314213042 : _
lem-box-cP-at0314213042 = D016.lem-box-cP-at0314213042 sD016
lem-sym-bc-at0214213043 : _
lem-sym-bc-at0214213043 = D016.lem-sym-bc-at0214213043 sD016
lem-sym-bc-at1331 : _
lem-sym-bc-at1331 = D016.lem-sym-bc-at1331 sD016
lem-pairs-at032032 : _
lem-pairs-at032032 = D016.lem-pairs-at032032 sD016
lem-sym-bc-at0312243140 : _
lem-sym-bc-at0312243140 = D016.lem-sym-bc-at0312243140 sD016
lem-sym-bc-at0312213440 : _
lem-sym-bc-at0312213440 = D016.lem-sym-bc-at0312213440 sD016
lem-box-cP-at0312243140 : _
lem-box-cP-at0312243140 = D016.lem-box-cP-at0312243140 sD016
lem-sym-bc-at132132 : _
lem-sym-bc-at132132 = D016.lem-sym-bc-at132132 sD016
lem-sym-bc-at022330 : _
lem-sym-bc-at022330 = D016.lem-sym-bc-at022330 sD016
lem-pairs-at0220 : _
lem-pairs-at0220 = D016.lem-pairs-at0220 sD016
lem-sym-bc-at0213213440 : _
lem-sym-bc-at0213213440 = D016.lem-sym-bc-at0213213440 sD016
lem-pairs-at0213243140 : _
lem-pairs-at0213243140 = D016.lem-pairs-at0213243140 sD016
lem-box-cP-at022330 : _
lem-box-cP-at022330 = D016.lem-box-cP-at022330 sD016
lem-sym-bc-at122331 : _
lem-sym-bc-at122331 = D016.lem-sym-bc-at122331 sD016
lem-box-cP-at14213243 : _
lem-box-cP-at14213243 = D016.lem-box-cP-at14213243 sD016
lem-sym-bc-at12233441 : _
lem-sym-bc-at12233441 = D016.lem-sym-bc-at12233441 sD016
lem-sym-bc-at2332 : _
lem-sym-bc-at2332 = D016.lem-sym-bc-at2332 sD016
lem-box-perm-1324-at03102132 : _
lem-box-perm-1324-at03102132 = D016.lem-box-perm-1324-at03102132 sD016
sD018 : SD018
sD018 = (λ c → lem-comm-CS03-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CS12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CS13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CS14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CS23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CS24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-CSd03-CCZ124 (lit c)) ∷ᵃ (λ c → lem-comm-CSd04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CSd24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-CX12-TOFF034 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF013-CSd24 (lit c)) ∷ᵃ (λ c → lem-comm-CK40-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CK41-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CK42-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-CS04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CX40-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF213-CK40 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF213-CSd04 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF312-CS04 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF023-CK41 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF023-CSd14 (lit c)) ∷ᵃ lem-sym-ab ∷ᵃ lem-sym-ab-at032032 ∷ᵃ lem-sym-ab-at04203243 ∷ᵃ lem-sym-ab-at1221 ∷ᵃ lem-sym-ab-at122331 ∷ᵃ lem-sym-ab-at12233441 ∷ᵃ lem-sym-ab-at122441 ∷ᵃ lem-sym-ab-at2332 ∷ᵃ lem-sym-ab-at233442 ∷ᵃ lem-box-tQ-at0410213243 ∷ᵃ lem-box-tQ-at13243142 ∷ᵃ lem-box-tQ-at13243241 ∷ᵃ lem-box-tQ-at14233142 ∷ᵃ lem-box-tQ ∷ᵃ lem-box-tQ-at0210233441 ∷ᵃ lem-box-tQ-at0210243143 ∷ᵃ lem-box-tQ-at0310243142 ∷ᵃ lem-box-tQ-at0330 ∷ᵃ lem-box-tQ-at043043 ∷ᵃ lem-box-tQ-at12243143 ∷ᵃ lem-box-tQ-at122441 ∷ᵃ lem-box-tQ-at1441 ∷ᵃ lem-box-tQ-at233442 ∷ᵃ lem-box-tQ-at243243 ∷ᵃ lem-box-tQ-at2442 ∷ᵃ lem-P-box ∷ᵃ lem-P-box-at0214213043 ∷ᵃ lem-P-box-at0310243142 ∷ᵃ lem-P-box-at0330 ∷ᵃ lem-P-box-at1221 ∷ᵃ lem-P-box-at122331 ∷ᵃ lem-P-box-at132132 ∷ᵃ lem-P-box-at13213442 ∷ᵃ lem-P-box-at1331 ∷ᵃ lem-P-box-at2332 ∷ᵃ lem-P-box-at3443 ∷ᵃ lem-t-cP ∷ᵃ lem-t-cP-at0210243143 ∷ᵃ lem-t-cP-at043043 ∷ᵃ lem-t-cP-at122441 ∷ᵃ lem-t-cP-at243243 ∷ᵃ lem-P-box-at143143 ∷ᵃ lem-CXu-box-4-at03102132 ∷ᵃ lem-box-cP ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at0214213043 ∷ᵃ lem-box-cP-at0310243142 ∷ᵃ lem-box-cP-at0314203142 ∷ᵃ lem-box-cP-at0330 ∷ᵃ lem-box-cP-at043043 ∷ᵃ lem-box-cP-at1221 ∷ᵃ lem-box-cP-at122331 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at132132 ∷ᵃ lem-box-cP-at13213442 ∷ᵃ lem-box-cP-at1331 ∷ᵃ lem-box-cP-at143143 ∷ᵃ lem-box-cP-at2332 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-cP-at3443 ∷ᵃ lem-pairs-at13243142 ∷ᵃ lem-pairs-at13243241 ∷ᵃ lem-pairs-at14233241 ∷ᵃ lem-sym-bc ∷ᵃ lem-sym-bc-at0210243143 ∷ᵃ lem-sym-bc-at0330 ∷ᵃ lem-sym-bc-at043043 ∷ᵃ lem-sym-bc-at1221 ∷ᵃ lem-sym-bc-at122441 ∷ᵃ lem-sym-bc-at13213442 ∷ᵃ lem-sym-bc-at133441 ∷ᵃ lem-sym-bc-at1441 ∷ᵃ lem-sym-bc-at243243 ∷ᵃ nil
lem-Xb-box-at0210243143 : _
lem-Xb-box-at0210243143 = D018.lem-Xb-box-at0210243143 sD018
lem-box2-at0210243143 : _
lem-box2-at0210243143 = D018.lem-box2-at0210243143 sD018
lem-Xb-box-at243243 : _
lem-Xb-box-at243243 = D018.lem-Xb-box-at243243 sD018
lem-box2-at243243 : _
lem-box2-at243243 = D018.lem-box2-at243243 sD018
lem-Xb-box-at122441 : _
lem-Xb-box-at122441 = D018.lem-Xb-box-at122441 sD018
lem-box2-at122441 : _
lem-box2-at122441 = D018.lem-box2-at122441 sD018
lem-pairs : _
lem-pairs = D018.lem-pairs sD018
lem-pairs-at1221 : _
lem-pairs-at1221 = D018.lem-pairs-at1221 sD018
lem-pairs-at2332 : _
lem-pairs-at2332 = D018.lem-pairs-at2332 sD018
lem-pairs-at122331 : _
lem-pairs-at122331 = D018.lem-pairs-at122331 sD018
lem-pairs-at132132 : _
lem-pairs-at132132 = D018.lem-pairs-at132132 sD018
lem-pairs-at13213442 : _
lem-pairs-at13213442 = D018.lem-pairs-at13213442 sD018
lem-pairs-at1331 : _
lem-pairs-at1331 = D018.lem-pairs-at1331 sD018
lem-Ku-box : _
lem-Ku-box = D018.lem-Ku-box sD018
lem-Kdu-box : _
lem-Kdu-box = D018.lem-Kdu-box sD018
lem-CSu-box-3 : _
lem-CSu-box-3 = D018.lem-CSu-box-3 sD018
lem-CSdu-box-3 : _
lem-CSdu-box-3 = D018.lem-CSdu-box-3 sD018
lem-CSu-box-4 : _
lem-CSu-box-4 = D018.lem-CSu-box-4 sD018
lem-CSdu-box-4 : _
lem-CSdu-box-4 = D018.lem-CSdu-box-4 sD018
lem-pairs-at3443 : _
lem-pairs-at3443 = D018.lem-pairs-at3443 sD018
lem-CSdu-box-3-at043043 : _
lem-CSdu-box-3-at043043 = D018.lem-CSdu-box-3-at043043 sD018
lem-pairs-at0330 : _
lem-pairs-at0330 = D018.lem-pairs-at0330 sD018
lem-pairs-at0310243142 : _
lem-pairs-at0310243142 = D018.lem-pairs-at0310243142 sD018
lem-Ku-box-at243243 : _
lem-Ku-box-at243243 = D018.lem-Ku-box-at243243 sD018
lem-Kdu-box-at243243 : _
lem-Kdu-box-at243243 = D018.lem-Kdu-box-at243243 sD018
lem-Ku-box-at122441 : _
lem-Ku-box-at122441 = D018.lem-Ku-box-at122441 sD018
lem-Kdu-box-at122441 : _
lem-Kdu-box-at122441 = D018.lem-Kdu-box-at122441 sD018
lem-pairs-at0214213043 : _
lem-pairs-at0214213043 = D018.lem-pairs-at0214213043 sD018
lem-box-perm-1324-at122441 : _
lem-box-perm-1324-at122441 = D018.lem-box-perm-1324-at122441 sD018
lem-Ku-box-at0210243143 : _
lem-Ku-box-at0210243143 = D018.lem-Ku-box-at0210243143 sD018
lem-Kdu-box-at0210243143 : _
lem-Kdu-box-at0210243143 = D018.lem-Kdu-box-at0210243143 sD018
lem-pairs-at143143 : _
lem-pairs-at143143 = D018.lem-pairs-at143143 sD018
lem-box-perm-1324-at0210243143 : _
lem-box-perm-1324-at0210243143 = D018.lem-box-perm-1324-at0210243143 sD018
lem-box-perm-1324-at243243 : _
lem-box-perm-1324-at243243 = D018.lem-box-perm-1324-at243243 sD018
lem-box-perm-1423-at122441 : _
lem-box-perm-1423-at122441 = D018.lem-box-perm-1423-at122441 sD018
sD019 : SD019
sD019 = (λ c → lem-comm-CS12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CS13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CS23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CSd12-CCZ034 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX04-CCZ123 (lit c)) ∷ᵃ (λ c → lem-comm-CX04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CX13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CCZ024-CX13 (lit c)) ∷ᵃ (λ c → lem-comm-CS02-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-CS14-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CSd02-CCZ134 (lit c)) ∷ᵃ (λ c → lem-comm-CSd14-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CX04-TOFF312 (lit c)) ∷ᵃ (λ c → lem-comm-CX30-TOFF214 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF013-CK42 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF213-CX04 (lit c)) ∷ᵃ lem-sym-ab-at0210243143 ∷ᵃ lem-sym-ab-at0214203143 ∷ᵃ lem-sym-ab-at03102132 ∷ᵃ lem-sym-ab-at0310243142 ∷ᵃ lem-sym-ab-at0312213440 ∷ᵃ lem-sym-ab-at0314203142 ∷ᵃ lem-sym-ab-at122441 ∷ᵃ lem-sym-ab-at021021 ∷ᵃ lem-sym-ab-at0213213440 ∷ᵃ lem-sym-ab-at0220 ∷ᵃ lem-sym-ab-at02233440 ∷ᵃ lem-sym-ab-at14233241 ∷ᵃ lem-box-tQ-at032032 ∷ᵃ lem-box-tQ-at0210243143 ∷ᵃ lem-box-tQ-at0214213043 ∷ᵃ lem-box-tQ-at022330 ∷ᵃ lem-box-tQ-at0310243142 ∷ᵃ lem-box-tQ-at0314213042 ∷ᵃ lem-box-tQ-at122331 ∷ᵃ lem-P-box-at0210233441 ∷ᵃ lem-P-box-at0210243143 ∷ᵃ lem-P-box-at022330 ∷ᵃ lem-P-box-at0312243140 ∷ᵃ lem-P-box-at243243 ∷ᵃ lem-t-cP-at0314213042 ∷ᵃ lem-sym-bc-at0213243140 ∷ᵃ lem-box-cP-at0210233441 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at0213203441 ∷ᵃ lem-box-cP-at022330 ∷ᵃ lem-box-cP-at0310243142 ∷ᵃ lem-box-cP-at0312243140 ∷ᵃ lem-box-cP-at0314213042 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-pairs-at0213243140 ∷ᵃ lem-pairs-at0220 ∷ᵃ lem-pairs-at032032 ∷ᵃ lem-pairs-at13243241 ∷ᵃ lem-sym-bc-at0213213440 ∷ᵃ lem-sym-bc-at0214203143 ∷ᵃ lem-sym-bc-at0214213043 ∷ᵃ lem-sym-bc-at0312243140 ∷ᵃ lem-sym-bc-at0314203142 ∷ᵃ lem-sym-bc-at0314213042 ∷ᵃ lem-sym-bc-at1441 ∷ᵃ nil
lem-pairs-at0210233441 : _
lem-pairs-at0210233441 = D019.lem-pairs-at0210233441 sD019
lem-CSdu-box-3-at0314213042 : _
lem-CSdu-box-3-at0314213042 = D019.lem-CSdu-box-3-at0314213042 sD019
lem-CXu-box-4-at0210243143 : _
lem-CXu-box-4-at0210243143 = D019.lem-CXu-box-4-at0210243143 sD019
lem-pairs-at243243 : _
lem-pairs-at243243 = D019.lem-pairs-at243243 sD019
lem-pairs-at0312243140 : _
lem-pairs-at0312243140 = D019.lem-pairs-at0312243140 sD019
lem-pairs-at0210243143 : _
lem-pairs-at0210243143 = D019.lem-pairs-at0210243143 sD019
lem-box-perm-2341-at021021 : _
lem-box-perm-2341-at021021 = D019.lem-box-perm-2341-at021021 sD019
lem-box-perm-4123-at02233440 : _
lem-box-perm-4123-at02233440 = D019.lem-box-perm-4123-at02233440 sD019
lem-pairs-at022330 : _
lem-pairs-at022330 = D019.lem-pairs-at022330 sD019
sD020 : SD020
sD020 = (λ c → lem-comm-CS13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CS23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CS24-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CSd24-CCZ013 (lit c)) ∷ᵃ (λ c → lem-comm-CX13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CX23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-CCZ014-CX23 (lit c)) ∷ᵃ (λ c → lem-comm-CCZ024-CX13 (lit c)) ∷ᵃ (λ c → lem-comm-CCZ024-CX31 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF013-CX24 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF213-CX04 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF023-CX14 (lit c)) ∷ᵃ lem-sym-ab-at132132 ∷ᵃ lem-box-tQ-at12233441 ∷ᵃ lem-box-tQ-at132132 ∷ᵃ lem-box-tQ-at14213243 ∷ᵃ lem-P-box-at12233441 ∷ᵃ lem-P-box-at122441 ∷ᵃ lem-P-box-at14213243 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at12233441 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at14213243 ∷ᵃ lem-box-cP-at2332 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-perm-1324-at03102132 ∷ᵃ lem-sym-bc-at0330 ∷ᵃ lem-sym-bc-at2332 ∷ᵃ nil
lem-pairs-at14213243 : _
lem-pairs-at14213243 = D020.lem-pairs-at14213243 sD020
lem-pairs-at12233441 : _
lem-pairs-at12233441 = D020.lem-pairs-at12233441 sD020
lem-pairs-at122441 : _
lem-pairs-at122441 = D020.lem-pairs-at122441 sD020
sD025 : SD025
sD025 = (λ c → lem-comm-CS03-TOFF412 (lit c)) ∷ᵃ (λ c → lem-comm-CS13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CS23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CSd13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CSd23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX04-TOFF213 (lit c)) ∷ᵃ (λ c → lem-comm-CX13-CCZ024 (lit c)) ∷ᵃ (λ c → lem-comm-CX14-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CX23-CCZ014 (lit c)) ∷ᵃ (λ c → lem-comm-CX24-TOFF013 (lit c)) ∷ᵃ (λ c → lem-comm-CK41-CCZ023 (lit c)) ∷ᵃ (λ c → lem-comm-CK41-TOFF023 (lit c)) ∷ᵃ (λ c → lem-comm-CS02-TOFF314 (lit c)) ∷ᵃ (λ c → lem-comm-CX21-TOFF034 (lit c)) ∷ᵃ (λ c → lem-comm-TOFF214-CS03 (lit c)) ∷ᵃ (λ c → lem-comm-CCZ023-CK41 (lit c)) ∷ᵃ lem-sym-ab ∷ᵃ lem-sym-ab-at0210233441 ∷ᵃ lem-sym-ab-at0210243143 ∷ᵃ lem-sym-ab-at0213203441 ∷ᵃ lem-sym-ab-at03102132 ∷ᵃ lem-sym-ab-at0310243142 ∷ᵃ lem-sym-ab-at0314203142 ∷ᵃ lem-sym-ab-at032032 ∷ᵃ lem-sym-ab-at033440 ∷ᵃ lem-sym-ab-at1221 ∷ᵃ lem-sym-ab-at122331 ∷ᵃ lem-sym-ab-at12243143 ∷ᵃ lem-sym-ab-at13213442 ∷ᵃ lem-sym-ab-at13243142 ∷ᵃ lem-sym-ab-at13243241 ∷ᵃ lem-sym-ab-at133441 ∷ᵃ lem-sym-ab-at14233142 ∷ᵃ lem-sym-ab-at2332 ∷ᵃ lem-sym-ab-at243243 ∷ᵃ lem-sym-ab-at021021 ∷ᵃ lem-sym-ab-at0220 ∷ᵃ lem-sym-ab-at132132 ∷ᵃ lem-sym-ab-at1331 ∷ᵃ lem-sym-ab-at14213243 ∷ᵃ lem-box-tQ-at0314213042 ∷ᵃ lem-box-tQ-at043043 ∷ᵃ lem-box-tQ-at12233441 ∷ᵃ lem-box-tQ-at02233440 ∷ᵃ lem-CSdu-box-1 ∷ᵃ lem-CSdu-box-2 ∷ᵃ lem-CSdu-box-2-at0210243143 ∷ᵃ lem-CSdu-box-2-at122441 ∷ᵃ lem-CSdu-box-2-at243243 ∷ᵃ lem-CSu-box-1 ∷ᵃ lem-CSu-box-2 ∷ᵃ lem-CSu-box-2-at122441 ∷ᵃ lem-CSu-box-2-at243243 ∷ᵃ lem-Sdu-box ∷ᵃ lem-Su-box ∷ᵃ lem-CSu-box-2-at0210243143 ∷ᵃ lem-box-cP-at0210213443 ∷ᵃ lem-sym-bc-at0220 ∷ᵃ lem-sym-bc-at032032 ∷ᵃ lem-sym-bc-at13243142 ∷ᵃ lem-sym-bc-at13243241 ∷ᵃ lem-sym-bc-at14233142 ∷ᵃ lem-box-cP-at0210243143 ∷ᵃ lem-box-cP-at1221 ∷ᵃ lem-box-cP-at12213443 ∷ᵃ lem-box-cP-at12233441 ∷ᵃ lem-box-cP-at122441 ∷ᵃ lem-box-cP-at243243 ∷ᵃ lem-box-cP-at3443 ∷ᵃ lem-pairs-at13243142 ∷ᵃ lem-pairs-at14233142 ∷ᵃ lem-sym-bc ∷ᵃ lem-sym-bc-at0214203143 ∷ᵃ lem-sym-bc-at022330 ∷ᵃ lem-sym-bc-at0312213440 ∷ᵃ lem-sym-bc-at0330 ∷ᵃ lem-sym-bc-at1221 ∷ᵃ lem-sym-bc-at122331 ∷ᵃ lem-sym-bc-at12233441 ∷ᵃ lem-sym-bc-at12243143 ∷ᵃ lem-sym-bc-at122441 ∷ᵃ lem-sym-bc-at132132 ∷ᵃ lem-sym-bc-at1331 ∷ᵃ lem-sym-bc-at14213243 ∷ᵃ lem-sym-bc-at2332 ∷ᵃ lem-CSdu-box-3 ∷ᵃ lem-CSdu-box-3-at043043 ∷ᵃ lem-CSdu-box-4 ∷ᵃ lem-CSu-box-3 ∷ᵃ lem-CSu-box-4 ∷ᵃ lem-Kdu-box ∷ᵃ lem-Kdu-box-at0210243143 ∷ᵃ lem-Kdu-box-at122441 ∷ᵃ lem-Kdu-box-at243243 ∷ᵃ lem-Ku-box ∷ᵃ lem-Ku-box-at0210243143 ∷ᵃ lem-Ku-box-at122441 ∷ᵃ lem-Ku-box-at243243 ∷ᵃ lem-Xb-box-at0210243143 ∷ᵃ lem-Xb-box-at122441 ∷ᵃ lem-Xb-box-at243243 ∷ᵃ lem-box-perm-1324-at0210243143 ∷ᵃ lem-box-perm-1324-at122441 ∷ᵃ lem-box-perm-1324-at243243 ∷ᵃ lem-box-perm-1423-at122441 ∷ᵃ lem-box2-at0210243143 ∷ᵃ lem-box2-at122441 ∷ᵃ lem-box2-at243243 ∷ᵃ lem-pairs ∷ᵃ lem-pairs-at0214213043 ∷ᵃ lem-pairs-at0310243142 ∷ᵃ lem-pairs-at0330 ∷ᵃ lem-pairs-at1221 ∷ᵃ lem-pairs-at122331 ∷ᵃ lem-pairs-at132132 ∷ᵃ lem-pairs-at13213442 ∷ᵃ lem-pairs-at1331 ∷ᵃ lem-pairs-at143143 ∷ᵃ lem-pairs-at2332 ∷ᵃ lem-pairs-at3443 ∷ᵃ lem-CSdu-box-3-at0314213042 ∷ᵃ lem-CXu-box-4-at0210243143 ∷ᵃ lem-box-perm-2341-at021021 ∷ᵃ lem-box-perm-4123-at02233440 ∷ᵃ lem-pairs-at0210233441 ∷ᵃ lem-pairs-at0210243143 ∷ᵃ lem-pairs-at022330 ∷ᵃ lem-pairs-at0312243140 ∷ᵃ lem-pairs-at243243 ∷ᵃ lem-pairs-at12233441 ∷ᵃ lem-pairs-at122441 ∷ᵃ lem-pairs-at14213243 ∷ᵃ nil
lem-F5-01 : _
lem-F5-01 = D025.lem-F5-01 sD025
lem-F5-12 : _
lem-F5-12 = D025.lem-F5-12 sD025
lem-F5-23 : _
lem-F5-23 = D025.lem-F5-23 sD025
