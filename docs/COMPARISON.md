# Comparison of SCXML Interpreters

In this document, I will make an attempt to compare and measure the performance
of the various, freely available SCXML interpreters. If you are the author of
one of these interpreters and feel that I misrepresented your work, please do
not hesitate to contact me and I will reevaluate / correct any factual errors.

This selection is based on the list of available implementations on the [SCXML
wiki](https://en.wikipedia.org/wiki/SCXML) page, plus a few interpreters I know
from the [W3C mailing list](https://lists.w3.org/Archives/Public/www-voice/)
and the [SCXML workshops](http://scxmlworkshop.de). I will list all
interpreters known to me, but only benchmark those that pass the W3C IRP tests
as is required for an actual SCXML interpreter.

# Methodology

The benchmarks were performed with a [huge
SCXML](https://github.com/tklab-tud/uscxml/tree/master/test/w3c/compound) file
containing all of the automatic W3C IRP tests that do not rely on timeouts to
pass.

## scxmlcc

| Platforms     | Tested on           | Tested           | Website       |
|---------------|---------------------|------------------|---------------|
| Linux only    | Debian Jessie 64Bit | **No**: Subset of SCXML implemented is insufficient for SCXML IRP tests. | [http://scxmlcc.org](http://scxmlcc.org) |

### How to build

    $ sudo apt-get install build-essential libboost-all-dev autorevision
    $ git clone https://github.com/jp-embedded/scxmlcc.git
    $ cd scxmlcc/src
    $ make
    
### Evaluation

    $ ./scxmlcc -i ./test-ecma-all.scxml |sort |uniq
    warning: event asteriks not currently supported
    warning: event tokens not currently supported
    warning: parallel support is not fully implemented/tested
    warning: unknown action type 'script'
    warning: unknown item 'assign' in <onentry> or <onexit>
    warning: unknown item 'assign' in <transition>
    warning: unknown item 'cancel' in <transition>
    warning: unknown item 'datamodel' in <state>
    warning: unknown item 'donedata' in <state>
    warning: unknown item 'foreach' in <onentry> or <onexit>
    warning: unknown item 'if' in <onentry> or <onexit>
    warning: unknown item 'invoke' in <state>
    warning: unknown item 'send' in <onentry> or <onexit>
    warning: unknown item 'send' in <transition>

The subset of SCXML implemented in <tt>scxmlcc</tt> is insufficient to run the
performance / compliance benchmarks.

## SCXML Lab

| Platforms     | Tested on           | Tested    | Website       |
|---------------|---------------------|-----------|---------------|
| HTML5         | Safari 9.0.3        | **No**: Subset of SCXML implemented is insufficient for SCXML IRP tests. | [http://www.ling.gu.se/~lager/Labs/SCXML-Lab/](http://www.ling.gu.se/~lager/Labs/SCXML-Lab/) |

I pasted the file above into their web-frontend and got a <tt>validation-error</tt>

    Unexpected attribute 'datamodel' in <scxml>. Hint: 
    Valid attributes are: 'id', 'initialstate', 'version', 'xmlns'.

The <tt>datamodel</tt> is indeed not required for a compliant interpreter, but
we will not be able to pass any meaningful subset of the SCXML IRP tests
without support for a datamodel.

## Legian

| Platforms     | Tested on           | Tested    | Website       |
|---------------|---------------------|-----------|---------------|
| Java          | Java(TM) SE (build 1.8.0_45-b14) | **No**: Subset of SCXML implemented is insufficient for SCXML IRP tests. | [https://github.com/pelatimtt/Legian](https://github.com/pelatimtt/Legian/) |

Does not claim W3C compliance and will, therefore, not pass the compound IRP tests.

## Qt SCXML Engine

| Platforms     | Tested on           | Tested    | Website       |
|---------------|---------------------|-----------|---------------|
| Any           | Mac OSX 10.11.3 with Macports 2.3.4 | **No**: Subset of SCXML implemented is insufficient for SCXML IRP tests. | [https://qt.gitorious.org/qt-labs/scxml](https://qt.gitorious.org/qt-labs/scxml/) |

[No
support](https://qt.gitorious.org/qt-labs/scxml?p=qt-labs:scxml.git;a=blob_plain;f=doc/scxml.qdoc;hb=HEAD) 
for <tt>&lt;donedata></tt>, <tt>&lt;finalize></tt>. Furthermore the
<tt>profile</tt> (now <tt>datamodel</tt> with finalized SCXML recommendation) 
attribute is ignored.
