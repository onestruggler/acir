{-# OPTIONS --without-K --safe #-}

------------------------------------------------------------------------
-- Presentations of groups
--
-- The lemmas of Five/D that Resps uses, instantiated
--
-- Each derivation module takes the lemmas of the others that it uses
-- as a list (DSig); here every lemma that one uses, or that the
-- consumer does, is the lemma of its module applied to its list, in
-- dependency order.  Written by `scratchpad/four/di.py`.
------------------------------------------------------------------------

module Examples.Groups.Clifford+CS.Five.DAll.Resps where

open import Examples.Groups.Clifford+CS.Five.DSig
import Examples.Groups.Clifford+CS.Five.D.R001 as R001
import Examples.Groups.Clifford+CS.Five.D.R002 as R002
import Examples.Groups.Clifford+CS.Five.D.R003 as R003
import Examples.Groups.Clifford+CS.Five.D.R004 as R004
import Examples.Groups.Clifford+CS.Five.D.R005 as R005
import Examples.Groups.Clifford+CS.Five.D.R006 as R006
import Examples.Groups.Clifford+CS.Five.D.R007 as R007
import Examples.Groups.Clifford+CS.Five.D.R008 as R008
import Examples.Groups.Clifford+CS.Five.D.R009 as R009

lem-comm-push-CS04-sw1-R : _
lem-comm-push-CS04-sw1-R = R001.lem-comm-push-CS04-sw1-R
lem-comm-push-CS04-sw2-R : _
lem-comm-push-CS04-sw2-R = R001.lem-comm-push-CS04-sw2-R
lem-comm-push-CS04-sw1-L : _
lem-comm-push-CS04-sw1-L = R001.lem-comm-push-CS04-sw1-L
lem-comm-push-CS04-sw0-L : _
lem-comm-push-CS04-sw0-L = R001.lem-comm-push-CS04-sw0-L
lem-resp-CSd02-at-1 : _
lem-resp-CSd02-at-1 = R001.lem-resp-CSd02-at-1
lem-resp-CS02-at-1 : _
lem-resp-CS02-at-1 = R001.lem-resp-CS02-at-1
lem-resp-CCZ013-at-2 : _
lem-resp-CCZ013-at-2 = R001.lem-resp-CCZ013-at-2
lem-resp-TOFF103-at-2 : _
lem-resp-TOFF103-at-2 = R001.lem-resp-TOFF103-at-2
lem-resp-CZ14-at-2 : _
lem-resp-CZ14-at-2 = R001.lem-resp-CZ14-at-2
lem-resp-CCZ134-at-2 : _
lem-resp-CCZ134-at-2 = R001.lem-resp-CCZ134-at-2
lem-resp-CS14-at-3 : _
lem-resp-CS14-at-3 = R001.lem-resp-CS14-at-3
lem-resp-TOFF314-at-2 : _
lem-resp-TOFF314-at-2 = R001.lem-resp-TOFF314-at-2
lem-resp-CX13-at-2 : _
lem-resp-CX13-at-2 = R001.lem-resp-CX13-at-2
lem-comm-push-CSd04-sw0-L : _
lem-comm-push-CSd04-sw0-L = R001.lem-comm-push-CSd04-sw0-L
lem-comm-push-CSd04-sw1-L : _
lem-comm-push-CSd04-sw1-L = R001.lem-comm-push-CSd04-sw1-L
lem-resp-CSd13-at-2 : _
lem-resp-CSd13-at-2 = R001.lem-resp-CSd13-at-2
lem-comm-push-CX04-sw0-L : _
lem-comm-push-CX04-sw0-L = R001.lem-comm-push-CX04-sw0-L
lem-resp-CS03-at-1 : _
lem-resp-CS03-at-1 = R001.lem-resp-CS03-at-1
lem-resp-CSd03-at-1 : _
lem-resp-CSd03-at-1 = R001.lem-resp-CSd03-at-1
lem-comm-push-CS04-sw2-L : _
lem-comm-push-CS04-sw2-L = R001.lem-comm-push-CS04-sw2-L
lem-resp-CS03-at-2 : _
lem-resp-CS03-at-2 = R001.lem-resp-CS03-at-2
lem-resp-CS14-at-2 : _
lem-resp-CS14-at-2 = R001.lem-resp-CS14-at-2
lem-comm-push-CX04-sw1-L : _
lem-comm-push-CX04-sw1-L = R001.lem-comm-push-CX04-sw1-L
lem-resp-CSd14-at-2 : _
lem-resp-CSd14-at-2 = R001.lem-resp-CSd14-at-2
lem-resp-TOFF214-at-3 : _
lem-resp-TOFF214-at-3 = R001.lem-resp-TOFF214-at-3
lem-comm-push-CZ04-sw0-L : _
lem-comm-push-CZ04-sw0-L = R001.lem-comm-push-CZ04-sw0-L
lem-resp-CSd03-at-2 : _
lem-resp-CSd03-at-2 = R001.lem-resp-CSd03-at-2
lem-resp-CX14-at-2 : _
lem-resp-CX14-at-2 = R001.lem-resp-CX14-at-2
lem-resp-CCZ023-at-1 : _
lem-resp-CCZ023-at-1 = R001.lem-resp-CCZ023-at-1
lem-resp-CS13-at-2 : _
lem-resp-CS13-at-2 = R001.lem-resp-CS13-at-2
lem-resp-CS24-at-3 : _
lem-resp-CS24-at-3 = R001.lem-resp-CS24-at-3
lem-resp-CCZ124-at-3 : _
lem-resp-CCZ124-at-3 = R001.lem-resp-CCZ124-at-3
lem-resp-TOFF023-at-1 : _
lem-resp-TOFF023-at-1 = R001.lem-resp-TOFF023-at-1
lem-resp-TOFF134-at-2 : _
lem-resp-TOFF134-at-2 = R001.lem-resp-TOFF134-at-2
lem-resp-TOFF013-at-2 : _
lem-resp-TOFF013-at-2 = R001.lem-resp-TOFF013-at-2
lem-resp-TOFF203-at-1 : _
lem-resp-TOFF203-at-1 = R001.lem-resp-TOFF203-at-1
lem-comm-push-CSd04-sw2-L : _
lem-comm-push-CSd04-sw2-L = R001.lem-comm-push-CSd04-sw2-L
lem-resp-CX31-at-2 : _
lem-resp-CX31-at-2 = R001.lem-resp-CX31-at-2
lem-resp-CZ14-at-3 : _
lem-resp-CZ14-at-3 = R001.lem-resp-CZ14-at-3
lem-resp-TOFF302-at-1 : _
lem-resp-TOFF302-at-1 = R001.lem-resp-TOFF302-at-1
lem-resp-CZ24-at-3 : _
lem-resp-CZ24-at-3 = R001.lem-resp-CZ24-at-3
lem-resp-CX41-at-2 : _
lem-resp-CX41-at-2 = R001.lem-resp-CX41-at-2
lem-resp-CX41-at-3 : _
lem-resp-CX41-at-3 = R001.lem-resp-CX41-at-3
lem-resp-CSd24-at-3 : _
lem-resp-CSd24-at-3 = R001.lem-resp-CSd24-at-3
lem-resp-CX14-at-3 : _
lem-resp-CX14-at-3 = R001.lem-resp-CX14-at-3
lem-resp-SWAP14-at-2 : _
lem-resp-SWAP14-at-2 = R001.lem-resp-SWAP14-at-2
lem-resp-TOFF301-at-2 : _
lem-resp-TOFF301-at-2 = R001.lem-resp-TOFF301-at-2
lem-resp-CX42-at-3 : _
lem-resp-CX42-at-3 = R001.lem-resp-CX42-at-3
lem-resp-CSd14-at-3 : _
lem-resp-CSd14-at-3 = R001.lem-resp-CSd14-at-3
lem-resp-CX24-at-3 : _
lem-resp-CX24-at-3 = R001.lem-resp-CX24-at-3
lem-resp-SWAP14-at-3 : _
lem-resp-SWAP14-at-3 = R001.lem-resp-SWAP14-at-3
lem-resp-SWAP13-at-2 : _
lem-resp-SWAP13-at-2 = R001.lem-resp-SWAP13-at-2
lem-resp-CZ13-at-2 : _
lem-resp-CZ13-at-2 = R001.lem-resp-CZ13-at-2
lem-resp-CZ02-at-1 : _
lem-resp-CZ02-at-1 = R001.lem-resp-CZ02-at-1
lem-resp-CX20-at-1 : _
lem-resp-CX20-at-1 = R001.lem-resp-CX20-at-1
lem-resp-CX03-at-1 : _
lem-resp-CX03-at-1 = R001.lem-resp-CX03-at-1
lem-resp-CZ03-at-1 : _
lem-resp-CZ03-at-1 = R001.lem-resp-CZ03-at-1
lem-resp-CX30-at-1 : _
lem-resp-CX30-at-1 = R001.lem-resp-CX30-at-1
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
lem-resp-CX02-at-1 : _
lem-resp-CX02-at-1 = R001.lem-resp-CX02-at-1
lem-resp-TOFF412-at-3 : _
lem-resp-TOFF412-at-3 = R001.lem-resp-TOFF412-at-3
lem-resp-TOFF124-at-3 : _
lem-resp-TOFF124-at-3 = R001.lem-resp-TOFF124-at-3
lem-resp-CK41-at-2 : _
lem-resp-CK41-at-2 = R002.lem-resp-CK41-at-2
lem-comm-push-CK40-sw1-L : _
lem-comm-push-CK40-sw1-L = R002.lem-comm-push-CK40-sw1-L
lem-comm-push-CK40-sw2-L : _
lem-comm-push-CK40-sw2-L = R002.lem-comm-push-CK40-sw2-L
lem-resp-SWAP24-at-3 : _
lem-resp-SWAP24-at-3 = R002.lem-resp-SWAP24-at-3
lem-resp-TOFF413-at-2 : _
lem-resp-TOFF413-at-2 = R002.lem-resp-TOFF413-at-2
lem-resp-CX30-at-2 : _
lem-resp-CX30-at-2 = R002.lem-resp-CX30-at-2
lem-resp-CX03-at-2 : _
lem-resp-CX03-at-2 = R002.lem-resp-CX03-at-2
lem-comm-push-SWAP04-sw2-L : _
lem-comm-push-SWAP04-sw2-L = R002.lem-comm-push-SWAP04-sw2-L
lem-resp-SWAP03-at-2 : _
lem-resp-SWAP03-at-2 = R002.lem-resp-SWAP03-at-2
lem-resp-SWAP03-at-1 : _
lem-resp-SWAP03-at-1 = R002.lem-resp-SWAP03-at-1
lem-resp-CK41-at-3 : _
lem-resp-CK41-at-3 = R003.lem-resp-CK41-at-3
lem-resp-CK42-at-3 : _
lem-resp-CK42-at-3 = R003.lem-resp-CK42-at-3
lem-comm-push-SWAP04-sw0-L : _
lem-comm-push-SWAP04-sw0-L = R003.lem-comm-push-SWAP04-sw0-L
lem-comm-push-CX04-sw2-L : _
lem-comm-push-CX04-sw2-L = R003.lem-comm-push-CX04-sw2-L
lem-resp-SWAP02-at-1 : _
lem-resp-SWAP02-at-1 = R003.lem-resp-SWAP02-at-1
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
lem-resp-CZ03-at-2 : _
lem-resp-CZ03-at-2 = R003.lem-resp-CZ03-at-2
lem-resp-CK03-at-1 : _
lem-resp-CK03-at-1 = R004.lem-resp-CK03-at-1
lem-resp-CK02-at-1 : _
lem-resp-CK02-at-1 = R004.lem-resp-CK02-at-1
lem-resp-CK03-at-2 : _
lem-resp-CK03-at-2 = R004.lem-resp-CK03-at-2
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
lem-resp-CSd04-at-1 : _
lem-resp-CSd04-at-1 = R005.lem-resp-CSd04-at-1 sR005
lem-resp-CSd04-at-2 : _
lem-resp-CSd04-at-2 = R005.lem-resp-CSd04-at-2 sR005
lem-resp-CX04-at-1 : _
lem-resp-CX04-at-1 = R005.lem-resp-CX04-at-1 sR005
lem-comm-push-CCZ014-sw2-L : _
lem-comm-push-CCZ014-sw2-L = R005.lem-comm-push-CCZ014-sw2-L sR005
lem-resp-CX04-at-2 : _
lem-resp-CX04-at-2 = R005.lem-resp-CX04-at-2 sR005
lem-resp-CZ04-at-1 : _
lem-resp-CZ04-at-1 = R005.lem-resp-CZ04-at-1 sR005
lem-comm-push-TOFF024-sw0-L : _
lem-comm-push-TOFF024-sw0-L = R005.lem-comm-push-TOFF024-sw0-L sR005
lem-resp-CS04-at-2 : _
lem-resp-CS04-at-2 = R005.lem-resp-CS04-at-2 sR005
lem-resp-CS04-at-1 : _
lem-resp-CS04-at-1 = R005.lem-resp-CS04-at-1 sR005
lem-resp-CSd04-at-3 : _
lem-resp-CSd04-at-3 = R005.lem-resp-CSd04-at-3 sR005
lem-resp-CS04-at-3 : _
lem-resp-CS04-at-3 = R005.lem-resp-CS04-at-3 sR005
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
lem-resp-CZ04-at-3 : _
lem-resp-CZ04-at-3 = R006.lem-resp-CZ04-at-3 sR006
lem-resp-CX40-at-3 : _
lem-resp-CX40-at-3 = R006.lem-resp-CX40-at-3 sR006
lem-resp-CX40-at-1 : _
lem-resp-CX40-at-1 = R006.lem-resp-CX40-at-1 sR006
lem-resp-CK40-at-1 : _
lem-resp-CK40-at-1 = R006.lem-resp-CK40-at-1 sR006
lem-resp-CKd40-at-1 : _
lem-resp-CKd40-at-1 = R006.lem-resp-CKd40-at-1 sR006
lem-resp-CZ04-at-2 : _
lem-resp-CZ04-at-2 = R006.lem-resp-CZ04-at-2 sR006
lem-resp-CX40-at-2 : _
lem-resp-CX40-at-2 = R006.lem-resp-CX40-at-2 sR006
lem-resp-CK40-at-2 : _
lem-resp-CK40-at-2 = R006.lem-resp-CK40-at-2 sR006
lem-resp-CK40-at-3 : _
lem-resp-CK40-at-3 = R006.lem-resp-CK40-at-3 sR006
lem-comm-push-TOFF203-sw3-L : _
lem-comm-push-TOFF203-sw3-L = R006.lem-comm-push-TOFF203-sw3-L sR006
lem-comm-push-TOFF204-sw3-L : _
lem-comm-push-TOFF204-sw3-L = R006.lem-comm-push-TOFF204-sw3-L sR006
lem-comm-push-CCZ023-sw3-L : _
lem-comm-push-CCZ023-sw3-L = R006.lem-comm-push-CCZ023-sw3-L sR006
lem-comm-push-CCZ024-sw3-L : _
lem-comm-push-CCZ024-sw3-L = R006.lem-comm-push-CCZ024-sw3-L sR006
lem-comm-push-TOFF302-sw3-L : _
lem-comm-push-TOFF302-sw3-L = R006.lem-comm-push-TOFF302-sw3-L sR006
lem-comm-push-TOFF402-sw3-L : _
lem-comm-push-TOFF402-sw3-L = R006.lem-comm-push-TOFF402-sw3-L sR006
lem-resp-SWAP04-at-1 : _
lem-resp-SWAP04-at-1 = R006.lem-resp-SWAP04-at-1 sR006
lem-resp-CX04-at-3 : _
lem-resp-CX04-at-3 = R006.lem-resp-CX04-at-3 sR006
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
lem-resp-CCZ034-at-2 : _
lem-resp-CCZ034-at-2 = R009.lem-resp-CCZ034-at-2 sR009
lem-resp-CCZ034-at-1 : _
lem-resp-CCZ034-at-1 = R009.lem-resp-CCZ034-at-1 sR009
lem-resp-TOFF034-at-1 : _
lem-resp-TOFF034-at-1 = R009.lem-resp-TOFF034-at-1 sR009
lem-resp-TOFF034-at-2 : _
lem-resp-TOFF034-at-2 = R009.lem-resp-TOFF034-at-2 sR009
lem-resp-CCZ014-at-2 : _
lem-resp-CCZ014-at-2 = R009.lem-resp-CCZ014-at-2 sR009
lem-resp-TOFF204-at-1 : _
lem-resp-TOFF204-at-1 = R009.lem-resp-TOFF204-at-1 sR009
lem-resp-CCZ024-at-1 : _
lem-resp-CCZ024-at-1 = R009.lem-resp-CCZ024-at-1 sR009
lem-resp-CCZ024-at-3 : _
lem-resp-CCZ024-at-3 = R009.lem-resp-CCZ024-at-3 sR009
lem-resp-CCZ014-at-3 : _
lem-resp-CCZ014-at-3 = R009.lem-resp-CCZ014-at-3 sR009
lem-resp-TOFF014-at-2 : _
lem-resp-TOFF014-at-2 = R009.lem-resp-TOFF014-at-2 sR009
lem-resp-TOFF024-at-1 : _
lem-resp-TOFF024-at-1 = R009.lem-resp-TOFF024-at-1 sR009
lem-resp-TOFF024-at-3 : _
lem-resp-TOFF024-at-3 = R009.lem-resp-TOFF024-at-3 sR009
lem-resp-TOFF401-at-3 : _
lem-resp-TOFF401-at-3 = R009.lem-resp-TOFF401-at-3 sR009
lem-resp-TOFF304-at-2 : _
lem-resp-TOFF304-at-2 = R009.lem-resp-TOFF304-at-2 sR009
lem-resp-TOFF402-at-3 : _
lem-resp-TOFF402-at-3 = R009.lem-resp-TOFF402-at-3 sR009
lem-resp-TOFF304-at-1 : _
lem-resp-TOFF304-at-1 = R009.lem-resp-TOFF304-at-1 sR009
lem-resp-TOFF401-at-2 : _
lem-resp-TOFF401-at-2 = R009.lem-resp-TOFF401-at-2 sR009
lem-resp-TOFF204-at-3 : _
lem-resp-TOFF204-at-3 = R009.lem-resp-TOFF204-at-3 sR009
lem-resp-TOFF014-at-3 : _
lem-resp-TOFF014-at-3 = R009.lem-resp-TOFF014-at-3 sR009
lem-resp-TOFF403-at-2 : _
lem-resp-TOFF403-at-2 = R009.lem-resp-TOFF403-at-2 sR009
lem-resp-TOFF104-at-2 : _
lem-resp-TOFF104-at-2 = R009.lem-resp-TOFF104-at-2 sR009
lem-resp-TOFF104-at-3 : _
lem-resp-TOFF104-at-3 = R009.lem-resp-TOFF104-at-3 sR009
lem-resp-TOFF402-at-1 : _
lem-resp-TOFF402-at-1 = R009.lem-resp-TOFF402-at-1 sR009
lem-resp-TOFF403-at-1 : _
lem-resp-TOFF403-at-1 = R009.lem-resp-TOFF403-at-1 sR009
