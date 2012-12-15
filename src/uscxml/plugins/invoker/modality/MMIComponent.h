#ifndef MMICOMPONENT_H_MZ1I550N
#define MMICOMPONENT_H_MZ1I550N

#include "uscxml/Factory.h"

namespace uscxml {

class Interpreter;

class MMIComponent : public Invoker {
public:
	
  enum State {
		PAUSED,
		RUNNING,
		IDLE,
		TERMINATED
	};

	MMIComponent();
  virtual ~MMIComponent();
  virtual Invoker* create(Interpreter* interpreter);
  
  virtual Data getDataModelVariables();
  virtual void send(SendRequest& req);
  virtual void cancel(const std::string sendId);
  virtual void invoke(InvokeRequest& req);
  virtual void sendToParent(SendRequest& req);

protected:
  std::string _invokeId;
  Interpreter* _interpreter;

	State _state;
};


/** Base classes for MMI messages */

class MMICoreMessage {
public:
  std::string source;
  std::string target;
  std::string data;
  std::string requestId;
};

class MMICtxMessage : public MMICoreMessage {
public:
  std::string context;
};

class MMIStartMessage : public MMICtxMessage {
public:
  std::string content;
  std::string contentURL;
};

class MMISimpleStatusMessage : public MMICtxMessage {
public:
  std::string status;
};

class MMIStatusMessage : public MMISimpleStatusMessage {
public:
  std::string statusInfo;
};

/** Concrete MMI messages */

class MMINewContextRequest : public MMICoreMessage {};

/***/

class MMIPauseRequest : public MMICtxMessage {};
class MMIResumeRequest : public MMICtxMessage {};
class MMICancelRequest : public MMICtxMessage {};
class MMIClearContextRequest : public MMICtxMessage {};
class MMIStatusRequest : public MMICtxMessage {};

/***/

class MMIStartRequest : public MMIStartMessage {};
class MMIPrepareRequest : public MMIStartMessage {};

/***/

class MMIExtensionNotification : public MMICtxMessage {
  std::string name;
};

/***/

class MMIStatusResponse : public MMISimpleStatusMessage {};

/***/

class MMIStartResponse : public MMIStatusMessage {};
class MMIPrepareRespnse : public MMIStatusMessage {};
class MMIPauseResponse : public MMIStatusMessage {};
class MMIResumeResponse : public MMIStatusMessage {};
class MMICancelResponse : public MMIStatusMessage {};
class MMIDoneNotification : public MMIStatusMessage {};
class MMINewContextResponse : public MMIStatusMessage {};
class MMIClearContextResponse : public MMIStatusMessage {};

}

#endif /* end of include guard: MMICOMPONENT_H_MZ1I550N */
