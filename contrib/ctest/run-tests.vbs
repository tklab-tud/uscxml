Set shell    = CreateObject( "WScript.Shell" )
Set fso      = CreateObject("Scripting.FileSystemObject")
Set ip       = CreateObject("WScript.Network")
Set procEnv  = shell.Environment("Process")

ME_NAME  = Wscript.ScriptFullName
TEST_DIR = fso.GetParentFolderName(fso.GetFile(ME_NAME))
ACTUAL_CMD = TEST_DIR + "\..\..\test\ctest\run-tests.vbs"

if (NOT fso.FileExists(ACTUAL_CMD)) Then
	MsgBox "Could not find actual script at " + ACTUAL_CMD
	WScript.Quit
End If

shell.Run ACTUAL_CMD