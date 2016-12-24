import sys
import os.path


def main(argv):
    if not os.path.isfile(argv[1]):
        sys.exit(os.EX_NOINPUT)
    
    # where to find uscxmlNativePython.py?
    if os.path.exists('../../../build/cli/lib'):
        sys.path.append('../../../build/cli/lib')
    if os.environ.get('USCXML_PYTHON_PATH') and os.path.exists(os.environ['USCXML_PYTHON_PATH']):
        sys.path.append(os.environ['USCXML_PYTHON_PATH'])    
    
    import uscxmlNativePython as uscxml
    
    print "Processing" + argv[1]

    interpreter = uscxml.Interpreter.fromURL(argv[1]);
    state = interpreter.step()
    while state != uscxml.USCXML_FINISHED:
        state = interpreter.step()
    
    if interpreter.isInState("pass"):
        sys.exit(os.EX_OK)
        
    sys.exit(os.EX_OSERR)

if __name__ == "__main__":
    main(sys.argv)
