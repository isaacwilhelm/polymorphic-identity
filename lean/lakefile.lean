import Lake
open Lake DSL

package pi

@[default_target]
lean_lib PIFoundation

@[default_target]
lean_lib PIDerivations

@[default_target]
lean_lib PISchemas

@[default_target]
lean_lib PIExplore

@[default_target]
lean_lib PIHae

@[default_target]
lean_lib PITagged

@[default_target]
lean_lib PIBridge

@[default_target]
lean_lib PINew

@[default_target]
lean_lib PINF

@[default_target]
lean_lib PIGeneral

@[default_target]
lean_lib PISyntax

@[default_target]
lean_lib PIEnum

@[default_target]
lean_lib PICompleteness

@[default_target]
lean_lib PICanonical

@[default_target]
lean_lib PIModal

@[default_target]
lean_lib PIWorlds

@[default_target]
lean_lib PIAlg

@[default_target]
lean_lib PIAlgModels

@[default_target]
lean_lib PIAlgI

@[default_target]
lean_lib PIAlgIModels

@[default_target]
lean_lib PIBarcan

@[default_target]
lean_lib PIBarcanModels

@[default_target]
lean_lib PIClass

@[default_target]
lean_lib PIClassModels

@[default_target]
lean_lib PIKripke

@[default_target]
lean_lib PIKripkeModels

@[default_target]
lean_lib PIKripkeND

@[default_target]
lean_lib PIKripkeHae

@[default_target]
lean_lib PIKripkeCong

@[default_target]
lean_lib PINoSelf

@[default_target]
lean_lib PICongQs

@[default_target]
lean_lib PIHaeQs

@[default_target]
lean_lib PIModalX

@[default_target]
lean_lib PIModalX2

@[default_target]
lean_lib PIBF

@[default_target]
lean_lib PIOQ_KBF

@[default_target]
lean_lib PIOQ_Mr2

@[default_target]
lean_lib PIOQ_Mco

@[default_target]
lean_lib PIOQ_Der

@[default_target]
lean_lib PIOQ_Mcl

@[default_target]
lean_lib PIOQ_Mtt

@[default_target]
lean_lib PIOQ_MttT

@[default_target]
lean_lib PIOQ_MId

@[default_target]
lean_lib PIOQ_Small

@[default_target]
lean_lib PIOQ_Tow2

@[default_target]
lean_lib PIOQ_KIE

@[default_target]
lean_lib PIOQ_LLP

@[default_target]
lean_lib PIOQ_Swap

@[default_target]
lean_lib PIOQ_MIdB

@[default_target]
lean_lib PIOQ_DerBF

@[default_target]
lean_lib PIOQ_F3c

@[default_target]
lean_lib PIOQ_MtwNI

@[default_target]
lean_lib PIOQ_MSTc

@[default_target]
lean_lib PIOQ_P_Mii

@[default_target]
lean_lib PIOQ_P_Mpb

@[default_target]
lean_lib PIOQ_P_Mcb

@[default_target]
lean_lib PIOQ_P_McqC

@[default_target]
lean_lib PIOQ_P_Mint

@[default_target]
lean_lib PIOQ_P_McqA

@[default_target]
lean_lib PIOQ_P_MEkT

@[default_target]
lean_lib PIOQ_P_MieX

@[default_target]
lean_lib PIOQ_P_Mhb

@[default_target]
lean_lib PIOQ_P_Mtc

@[default_target]
lean_lib PIOQ_P_MKC

@[default_target]
lean_lib PIOQ_P_Mit

@[default_target]
lean_lib PIOQ_P_Mtb

@[default_target]
lean_lib PIOQ_P_Mtbx

@[default_target]
lean_lib PIOQ_P_MieC

@[default_target]
lean_lib PIOQ_P_MclH

@[default_target]
lean_lib PIOQ_P_Mhm

@[default_target]
lean_lib PIOQ_P_MbfK

@[default_target]
lean_lib PIOQ_P_MEk

@[default_target]
lean_lib PIOQ_P_Mhk

@[default_target]
lean_lib PIOQ_P_MhcN

@[default_target]
lean_lib PIOQ_P_MhwA

@[default_target]
lean_lib PIOQ_P_MhtT

@[default_target]
lean_lib PIOQ_P_MhwC

@[default_target]
lean_lib PIOQ_P_MhND

@[default_target]
lean_lib PIOQ_P_MhNI

@[default_target]
lean_lib PIOQ_P_Mhw

@[default_target]
lean_lib PIOQ_P_MhE

@[default_target]
lean_lib PIOQ_P_MqHC

@[default_target]
lean_lib PIOQ_P_Mht

@[default_target]
lean_lib PIOQ_P_MndH

@[default_target]
lean_lib PIOQ_P_MchH

@[default_target]
lean_lib PIOQ_P_MbfH

@[default_target]
lean_lib PIOQ_P_MTH

@[default_target]
lean_lib PIOQ_P_MCc

@[default_target]
lean_lib PIOQ_P_MbkH

@[default_target]
lean_lib PIOQ_P_MhieD

@[default_target]
lean_lib PIOQ_P_MqH

@[default_target]
lean_lib PIOQ_P_MhieC

@[default_target]
lean_lib PIOQ_P_ME2

@[default_target]
lean_lib PIOQ_P_MtwC

@[default_target]
lean_lib PIOQ_P_MNec

@[default_target]
lean_lib PIOQ_P_MBH

@[default_target]
lean_lib PIOQ_P_MKW1

@[default_target]
lean_lib PIOQ_P_MhaeC

@[default_target]
lean_lib PIOQ_DerNDX

@[default_target]
lean_lib PIOQ_DerCh

@[default_target]
lean_lib PIOQ_XInjW

@[default_target]
lean_lib PIOQ_XInjK

@[default_target]
lean_lib PIOQ_XModK

@[default_target]
lean_lib PIOQ_XIntK

@[default_target]
lean_lib PIOQ_XInjT

@[default_target]
lean_lib PIOQ_XPcT

@[default_target]
lean_lib PIOQ_XChK

@[default_target]
lean_lib PIOQ_XCanT

@[default_target]
lean_lib PIOQ_XTbT

@[default_target]
lean_lib PIOQ_XPeCh

@[default_target]
lean_lib PIOQ_XChW
