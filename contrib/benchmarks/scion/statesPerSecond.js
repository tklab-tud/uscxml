require('babel-polyfill');
let scxml = require('scxml');

function nowInMS() {
	var hrTime = process.hrtime();
	return hrTime[0] * 1000 + hrTime[1] / 1000000
}

var args = process.argv.splice(process.execArgv.length + 2);
var started = nowInMS();
var initTimeMs;

scxml.pathToModel(args[0], function(err,model){
  if(err) throw err;

  model.prepare(function(err, fnModel) {

  	var iterations = 0;
  	var mark = nowInMS();

    if(err) throw err;

    //instantiate the interpreter
    var sc = new scxml.scion.Statechart(fnModel);

		initTimeMs = nowInMS() - started;

		sc.registerListener({onEntry : function(stateId) {
				if (stateId == "mark") {
					iterations++;

					var now = nowInMS();
					if (now - mark > 1000) {
						console.log(initTimeMs + ", " + iterations);
						mark = now;
						iterations = 0;
					}

				}
			}
		});

    //start the interpreter
    sc.start();

    //send the init event
    sc.gen({name:"init",data:null});

  });
})