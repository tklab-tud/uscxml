Set shell    = CreateObject( "WScript.Shell" )
Set fso      = CreateObject("Scripting.FileSystemObject")
Set ip       = CreateObject("WScript.Network")
Set procEnv  = shell.Environment("Process")

' see http://stackoverflow.com/questions/4692542/force-a-vbs-to-run-using-cscript-instead-of-wscript
Sub forceCScriptExecution
    Dim Arg, Str
    If Not LCase( Right( WScript.FullName, 12 ) ) = "\cscript.exe" Then
        For Each Arg In WScript.Arguments
            If InStr( Arg, " " ) Then Arg = """" & Arg & """"
            Str = Str & " " & Arg
        Next
        shell.Run """" & VCVARSALL & """" & " && cscript //nologo """ & WScript.ScriptFullName & """" & Str
		WScript.Sleep 1000
        WScript.Quit
    End If
End Sub

ME_NAME  = Wscript.ScriptFullName
TEST_DIR = fso.GetParentFolderName(fso.GetFile(ME_NAME))
TESTS    = TEST_DIR + "\tests"
HOSTS    = TEST_DIR + "\hosts"
HOSTNAME = LCase(ip.ComputerName)
TESTFILE = HOSTS + "\" + HOSTNAME + ".ctest"

VCVARSALL = shell.ExpandEnvironmentStrings("%VCVARSALL%")
If VCVARSALL = "%VCVARSALL%" Then
	VCVARSALL = "C:\Program Files\Microsoft Visual Studio 10.0\VC\vcvarsall.bat"
End If
if (NOT fso.FileExists(VCVARSALL)) Then
	VCVARSALL = "C:\Program Files (x86)\Microsoft Visual Studio 10.0\VC\vcvarsall.bat"
End If

if (NOT fso.FileExists(VCVARSALL)) Then
	MsgBox("Please export %VCVARSALL% as the command to get a build environment for msvc.")
	WScript.Quit
End If

CTEST_SUBMIT_TYPE = shell.ExpandEnvironmentStrings("%CTEST_SUBMIT_TYPE%")
If CTEST_SUBMIT_TYPE = "%CTEST_SUBMIT_TYPE%" Then
	CTEST_SUBMIT_TYPE = "Experimental"
	procEnv("CTEST_SUBMIT_TYPE") = CTEST_SUBMIT_TYPE
End If

USCXML_SOURCE_DIR = shell.ExpandEnvironmentStrings("%USCXML_SOURCE_DIR%")
If USCXML_SOURCE_DIR = "%USCXML_SOURCE_DIR%" Then
	USCXML_SOURCE_DIR = fso.GetParentFolderName(fso.GetParentFolderName(TEST_DIR))
	procEnv("USCXML_SOURCE_DIR") = USCXML_SOURCE_DIR
End If

USCXML_SOURCE_DIR = shell.ExpandEnvironmentStrings("%USCXML_SOURCE_DIR%")
if (NOT fso.FileExists(USCXML_SOURCE_DIR + "\CMakeLists.txt")) Then
	MsgBox "Could not find uSCXML Source for " + ME_NAME
	WScript.Quit
End If

if (NOT fso.FileExists(TESTFILE)) Then
	MsgBox "Warning: Could not find test file for this host at " + TESTFILE + " - defaulting"
	TESTFILE = HOSTS + "\default.nmake.ctest"
End If

' continue with cscript
forceCScriptExecution

' Aqcuire lock to avoid concurrent builds
' this will throw a permission denied error :(

Set buildLock = fso.OpenTextFile(TESTFILE, 8, True)

' Check github for updates and quit when nothing's new
if (CTEST_SUBMIT_TYPE = "Continuous") Then
	shell.CurrentDirectory = USCXML_SOURCE_DIR
	Set oExec = shell.Exec("git pull")
	GIT_SYNC  = oExec.StdOut.ReadLine
	if (GIT_SYNC = "Already up-to-date.") Then
		WScript.Quit
	End If
End If

shell.CurrentDirectory = TEST_DIR
Set exec = shell.Exec("CMD /S /K ctest -VV --timeout 100 -S " + TESTFILE + " -DHOSTNAME=" + HOSTNAME + " 2>&1")
Do While exec.Status = 0
    WScript.Sleep 10
    WScript.StdOut.Write(exec.StdOut.ReadLine() & vbCRLF)
'    WScript.StdErr.Write(exec.StdErr.ReadLine())
Loop
