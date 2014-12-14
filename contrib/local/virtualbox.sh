#!/bin/bash

# VBoxManage startvm b307622e-6b5e-4e47-a427-84760cf2312b
#
# VBoxManage --nologo guestcontrol b307622e-6b5e-4e47-a427-84760cf2312b execute --image "C:\\Program/ Files\\Internet/ Explorer\\iexplore.exe" --username RailroadGuest --password bnsf1234 --wait-exit --wait-stdout
#
# VBoxManage controlvm b307622e-6b5e-4e47-a427-84760cf2312b savestate
#
# VBoxManage showvminfo b307622e-6b5e-4e47-a427-84760cf2312b | grep State
