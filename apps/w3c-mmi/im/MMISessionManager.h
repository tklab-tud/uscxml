#ifndef MMISESSIONMANAGER_H_IHDWUAKD
#define MMISESSIONMANAGER_H_IHDWUAKD

#include <uscxml/Interpreter.h>
#include <deque>
#include "../MMIEventServlet.h"

namespace uscxml {
	class MMISessionManager : public HTTPServlet {
	public:
		MMISessionManager(Interpreter interpreter);
		~MMISessionManager();
		
		class MMISession {
		public:
			Interpreter _interpreter;
			tthread::recursive_mutex _mutex;
			virtual void send(const SendRequest& req) = 0;
			virtual void receive(const Arabica::DOM::Node<std::string>& msg) = 0;
		};
		
		class CometMMISession : public MMISession {
		public:
			std::deque<SendRequest> _outQueue;
			HTTPServer::Request _longPollingReq;
			std::string _token;

			void send(const SendRequest& req);
			void receive(const Arabica::DOM::Node<std::string>& msg);
			void longPoll(const HTTPServer::Request& req);
		};
		
		class MMIIOProcessor : public IOProcessorImpl {
		public:
			MMIIOProcessor(MMISessionManager* sessionManager) : _sessionManager(sessionManager) {}
			
			// IOProcessorImpl
			virtual boost::shared_ptr<IOProcessorImpl> create(InterpreterImpl* interpreter);
			virtual std::list<std::string> getNames() {
				std::list<std::string> names;
				names.push_back("mmi.event");
				return names;
			}
			virtual Data getDataModelVariables();
			virtual void send(const SendRequest& req);
		protected:
			MMISessionManager* _sessionManager;
		};

		void send(const std::string& name, const SendRequest& req);

		/// HTTPServlet
		bool httpRecvRequest(const HTTPServer::Request& req);
		void setURL(const std::string& url) {
			_url = url;
		}
		std::string getURL() { return _url; }
		
		bool canAdaptPath() {
			return false;
		}
		
	protected:
		void received(const NewContextRequest& mmiEvent, const std::string& token = "");
		void received(const NewContextResponse& mmiEvent, const std::string& token = "");
		void received(const ExtensionNotification& mmiEvent);
		void received(const DoneNotification& mmiEvent);

		void setupHTMLClient(const HTTPServer::Request& req);
		
		Interpreter _protoInterpreter;
		Factory* _factory;
		DelayedEventQueue _eventQueue;
		std::map<std::string, MMISession*> _sessions;
		std::map<std::string, MMISession*> _tokens;
		std::string _url;
	};
}


#endif /* end of include guard: MMISESSIONMANAGER_H_IHDWUAKD */
