#!/bin/bash
cd /mnt/d/dwork3/acir/Examples/Groups/CCX+H/Rules3
for f in r1a r1b r1c r2a r2b r2c r2d r2e r2f r3a r3b r3c r3d r3e r3f r3g r4a r4b r4c r5a r6a r7a r7b r7c r7d₀ r7d₁; do
  python3 -B emit_family.py $f 60
done
echo ALLDONE
