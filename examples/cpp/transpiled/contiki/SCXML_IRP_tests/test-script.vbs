contiki_app_dir = "C:\Puneet\education\TU_Darmstadt\Theses\Attempt8\uscxml\apps\contiki\w3c_IRP_tests"
Const ip_address = "130.83.117.27"

Const ForReading = 1
Const ForWriting = 2
Set objFSO = CreateObject("Scripting.FileSystemObject")
objStartFolder = "input"
Set objFolder = objFSO.GetFolder(objStartFolder)
Set colFiles = objFolder.Files
previousFileName = "test144.c"

For Each objFile in colFiles
	Set objShell = WScript.CreateObject("WScript.Shell")
	'objFile.Copy(objFile.Name)
	Set objFile1 = objFSO.OpenTextFile("IRP_tests.cpp", ForReading)
	strText = objFile1.ReadAll
	objFile1.Close
	currentFileName = objFile.Name
	strNewText = Replace(strText, previousFileName, currentFileName)
	Set objFile1 = objFSO.OpenTextFile("IRP_tests.cpp", ForWriting)
	objFile1.WriteLine strNewText
	objFile1.Close
	previousFileName = currentFileName
	currentFileNameStem=Replace(currentFileName,".c","")
	cmd_to_build = "cmd /K CD" + contiki_app_dir + " & echo building contiki application for : "+currentFileNameStem+".scxml & make TARGET=win32 --debug=basic > logs\log_"+currentFileNameStem+".txt 2>&1 & exit"
	intReturn = objShell.Run(cmd_to_build, 2, True)
	' home: 192.168.137.1 university: 
	cmd_to_run = "cmd /K CD"+ contiki_app_dir +" & echo running : "+currentFileNameStem+".win32 & IRP_tests.win32 "+ip_address+" > output\output_"+currentFileNameStem+".txt 2>&1"
	Set oExec = objShell.Exec(cmd_to_run)
	WScript.Sleep(3000)
	oExec.Terminate
	'objFSO.DeleteFile(previousFileName)
	Set objShell = Nothing
Next