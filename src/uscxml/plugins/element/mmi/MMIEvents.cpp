/**
 *  @file
 *  @author     2012-2013 Stefan Radomski (stefan.radomski@cs.tu-darmstadt.de)
 *  @copyright  Simplified BSD
 *
 *  @cond
 *  This program is free software: you can redistribute it and/or modify
 *  it under the terms of the FreeBSD license as published by the FreeBSD
 *  project.
 *
 *  This program is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 *
 *  You should have received a copy of the FreeBSD license along with this
 *  program. If not, see <http://www.opensource.org/licenses/bsd-license>.
 *  @endcond
 */

#include "MMIEvents.h"

namespace uscxml {

void PrepareRequestElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void StartRequestElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void PauseRequestElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void ResumeRequestElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void CancelRequestElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void ClearContextRequestElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void StatusRequestElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void NewContextResponseElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void PrepareResponseElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void StartResponseElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void PauseResponseElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void ResumeResponseElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void CancelResponseElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void ClearContextResponseElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void StatusResponseElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void DoneNotificationElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void NewContextRequestElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}
void ExtensionNotificationElement::enterElement(const Arabica::DOM::Node<std::string>& node) {
}

}