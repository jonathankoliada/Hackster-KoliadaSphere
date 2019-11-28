/* Copyright (c) Microsoft Corporation. All rights reserved.
   Licensed under the MIT License. */

   // This sample C application for Azure Sphere demonstrates Azure IoT SDK C APIs
   // The application uses the Azure IoT SDK C APIs to
   // 1. Use the buttons to trigger sending telemetry to Azure IoT Hub/Central.
   // 2. Use IoT Hub/Device Twin to control an LED.

   // You will need to provide four pieces of information to use this application, all of which are set
   // in the app_manifest.json.
   // 1. The Scope Id for your IoT Central application (set in 'CmdArgs')
   // 2. The Tenant Id obtained from 'azsphere tenant show-selected' (set in 'DeviceAuthentication')
   // 3. The Azure DPS Global endpoint address 'global.azure-devices-provisioning.net'
   //    (set in 'AllowedConnections')
   // 4. The IoT Hub Endpoint address for your IoT Central application (set in 'AllowedConnections')

#include <signal.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdio.h>
#include <stdarg.h>
#include <errno.h>

// applibs_versions.h defines the API struct versions to use for applibs APIs.
#include "applibs_versions.h"
#include <applibs/log.h>
#include <applibs/networking.h>
#include <applibs/gpio.h>
#include <applibs/storage.h>
#include <applibs/uart.h>


// By default, this sample is targeted at the MT3620 Reference Development Board (RDB).
// This can be changed using the project property "Target Hardware Definition Directory".
// This #include imports the sample_hardware abstraction from that hardware definition.
#include <hw/sample_hardware.h>

#include "epoll_timerfd_utilities.h"

// Azure IoT SDK
#include <iothub_client_core_common.h>
#include <iothub_device_client_ll.h>
#include <iothub_client_options.h>
#include <iothubtransportmqtt.h>
#include <iothub.h>
#include <azure_sphere_provisioning.h>

static volatile sig_atomic_t terminationRequired = false;

#include "parson.h" // used to parse Device Twin messages.
//MOCKABLE_FUNCTION(, IOTHUB_CLIENT_RESULT, IoTHubDeviceClient_SetMessageCallback, IOTHUB_DEVICE_CLIENT_LL_HANDLE, iotHubClientHandle, IOTHUB_CLIENT_DEVICE_TWIN_CALLBACK, deviceTwinCallback, void*, userContextCallback);

// Azure IoT Hub/Central defines.
#define SCOPEID_LENGTH 20
static char scopeId[SCOPEID_LENGTH]; // ScopeId for the Azure IoT Central application, set in
									 // app_manifest.json, CmdArgs

static IOTHUB_DEVICE_CLIENT_LL_HANDLE iothubClientHandle = NULL;
static const int keepalivePeriodSeconds = 20;
static bool iothubAuthenticated = false;
static void SendMessageCallback(IOTHUB_CLIENT_CONFIRMATION_RESULT result, void *context);
static void ReceiveHubMessage(IOTHUB_CLIENT_CONFIRMATION_RESULT result, const unsigned char *payload, size_t payloadSize, void *userContextCallback);
static void TwinCallback(DEVICE_TWIN_UPDATE_STATE updateState, const unsigned char *payload,
	size_t payloadSize, void *userContextCallback);


static void TwinReportBoolState(const char *propertyName, bool propertyValue);
static void ReportStatusCallback(int result, void *context);
static const char *GetReasonString(IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason);
static const char *getAzureSphereProvisioningResultString(
	AZURE_SPHERE_PROV_RETURN_VALUE provisioningResult);
static void SendTelemetry(const unsigned char *key, const unsigned char *value);
static void SendRoomPressure(const unsigned char *value);
static void SendRoomHumidity(const unsigned char *value);
static void SendRoomTemperature(const unsigned char *value);
static void SendOutsidePressure(const unsigned char *value);
static void SendOutsideHumidity(const unsigned char *value);
static void SendOutsideTemperature(const unsigned char *value);
static void SendServerPressure(const unsigned char *value);
static void SendServerHumidity(const unsigned char *value);
static void SendServerTemperature(const unsigned char *value);
static void SendServerBattery(const unsigned char *value);
static void SendOutsideBattery(const unsigned char *value);
static void SendRoomBattery(const unsigned char *value);
static void SendInOffice(const unsigned char *value);
static void SendTrackerBattery(const unsigned char *value);
static void SendDoorState(const unsigned char *value);
static void SendDoorBattery(const unsigned char *value);

static void SendDoorState();

static void SetupAzureClient(void);

// Function to generate simulated Temperature data/telemetry
static void SendSimulatedTemperature(void);

// Initialization/Cleanup
static int InitPeripheralsAndHandlers(void);
static void ClosePeripheralsAndHandlers(void);

// File descriptors - initialized to invalid value
// Buttons
static int sendMessageButtonGpioFd = -1;
static int sendOrientationButtonGpioFd = -1;

// LED
static int deviceTwinStatusLedGpioFd = -1;
static bool statusLedOn = false;
static bool office_LED = false;
static bool outside_LED = false;
static bool server_LED = false;
static bool tracker_LED = false;


// Timer / polling
static int buttonPollTimerFd = -1;
static int azureTimerFd = -1;
static int epollFd = -1;

// Azure IoT poll periods
static const int AzureIoTDefaultPollPeriodSeconds = 5;
static const int AzureIoTMinReconnectPeriodSeconds = 60;
static const int AzureIoTMaxReconnectPeriodSeconds = 10 * 60;

static int azureIoTPollPeriodSeconds = -1;

// Button state variables
static GPIO_Value_Type sendMessageButtonState = GPIO_Value_High;
static GPIO_Value_Type sendOrientationButtonState = GPIO_Value_High;

static void ButtonPollTimerEventHandler(EventData *eventData);
static bool IsButtonPressed(int fd, GPIO_Value_Type *oldState);
static void SendMessageButtonHandler(void);
static void SendOrientationButtonHandler(void);
static bool deviceIsUp = false; // Orientation
static void AzureTimerEventHandler(EventData *eventData);

//UART STUFF
// File descriptors - initialized to invalid value
static int uartFd = -1;
static int gpioButtonFd = -1;
static int gpioButtonTimerFd = -1;
//static int epollFd = -1;

// State variables
static GPIO_Value_Type buttonState = GPIO_Value_High;

// Termination state
//static volatile sig_atomic_t terminationRequired = false;



/// <summary>
///     Signal handler for termination requests. This handler must be async-signal-safe.
/// </summary>
static void TerminationHandler(int signalNumber)
{
	// Don't use Log_Debug here, as it is not guaranteed to be async-signal-safe.
	terminationRequired = true;
}
static void SendUartMessage(int uartFd, const char *dataToSend)
{
	size_t totalBytesSent = 0;
	size_t totalBytesToSend = strlen(dataToSend);
	int sendIterations = 0;
	while (totalBytesSent < totalBytesToSend) {
		sendIterations++;

		// Send as much of the remaining data as possible
		size_t bytesLeftToSend = totalBytesToSend - totalBytesSent;
		const char *remainingMessageToSend = dataToSend + totalBytesSent;
		ssize_t bytesSent = write(uartFd, remainingMessageToSend, bytesLeftToSend);
		if (bytesSent < 0) {
			Log_Debug("ERROR: Could not write to UART: %s (%d).\n", strerror(errno), errno);
			terminationRequired = true;
			return;
		}

		totalBytesSent += (size_t)bytesSent;
	}
	//SendDoorState();
	Log_Debug("Sent %zu bytes over UART in %d calls.\n", totalBytesSent, sendIterations);
}

/// <summary>
///     Main entry point for this sample.
/// </summary>
char mydoorstate[1] = "";

int main(int argc, char *argv[])
{
	Log_Debug("IoT Hub/Central Application starting.\n");
	mydoorstate[0] = '0';
	if (argc == 2) {
		Log_Debug("Setting Azure Scope ID %s\n", argv[1]);
		strncpy(scopeId, argv[1], SCOPEID_LENGTH);
	}
	else {
		Log_Debug("ScopeId needs to be set in the app_manifest CmdArgs\n");
		return -1;
	}

	Log_Debug("UART application starting.\n");
	if (InitPeripheralsAndHandlers() != 0) {
		terminationRequired = true;
	}

	// Main loop
	while (!terminationRequired) {
		if (WaitForEventAndCallHandler(epollFd) != 0) {
			terminationRequired = true;
		}
	}

	ClosePeripheralsAndHandlers();

	Log_Debug("Application exiting.\n");

	return 0;
}

static void ButtonTimerEventHandler(EventData *eventData)
{
	if (ConsumeTimerFdEvent(gpioButtonTimerFd) != 0) {
		terminationRequired = true;
		return;
	}

	// Check for a button press
	GPIO_Value_Type newButtonState;
	int result = GPIO_GetValue(gpioButtonFd, &newButtonState);
	if (result != 0) {
		Log_Debug("ERROR: Could not read button GPIO: %s (%d).\n", strerror(errno), errno);
		terminationRequired = true;
		return;
	}

	// If the button has just been pressed, send data over the UART
	// The button has GPIO_Value_Low when pressed and GPIO_Value_High when released
	if (newButtonState != buttonState) {
		if (newButtonState == GPIO_Value_Low) {
			SendUartMessage(uartFd, "Hello world!\n");
		}
		buttonState = newButtonState;
	}
}

//const int messagesize = 35;
char message[100] = "";
char messageout[100] = "";

char value[100] = "";
char name[100] = "";
char value2[20] = "";
char name2[20] = "";
char a[5] = "";

int messagestart = 0;
int matchleft = 0;
int matchright = 0;
int e = 0;
int D = 0;
bool gotobracket = false;
bool gotoname = false;
bool recordstart = false;
bool recordnamestart = false;
int valuestart = 0;
int namestart = 0;

char evalue1[5] = "";
char evalue2[5] = "";
char evalue3[5] = "";
int got1 = 0;
int got2 = 0;

int evalue1start = 0;
int evalue2start = 0;
int evalue3start = 0;

int b = 0;
int button = 0;
int battery = 0;
char buttondata[1] = "";
int S = 0;
int door = 0;
int recordbatteryvalue = 0;
char batteryvalue[5] = "";
int batterystart = 0;
static void setevalue(const unsigned char *value) {

	for (int i = 0; i < sizeof(&value) - 1; i++) {
		if (value[i] == ',' && got1 == 1) {
			got2 = 1;
		}
		if (value[i] == ',' && got1 == 0) {
			got1 = 1;
		}
		if (got1 == 0 && got2 == 0) {
			if (evalue1start < 2) {
				evalue1[evalue1start] = value[i];
			}
			evalue1start++;
		}
		if (got1 == 1 && got2 == 0) {
			evalue2[evalue2start] = value[i];
			evalue2start++;
		}
		if (got1 == 1 && got2 == 1) {
			evalue3[evalue3start] = value[i];
			evalue3start++;
		}
	}

	Log_Debug("END OF SETVALUE Loop, our values are:\nTemperature: %s\nHumidity:%s\nPressure:%s\n", (char *)evalue1, (char *)evalue2, (char *)evalue3);

	evalue1start = 0;
	evalue2start = 0;
	evalue3start = 0;
	got1 = 0;
	got2 = 0;
}

//Handler that 
static void UartEventHandler(EventData *eventData)
{
	const size_t receiveBufferSize = 128;
	uint8_t receiveBuffer[receiveBufferSize + 1]; // allow extra byte for string termination
	ssize_t bytesRead = -1;

	for (int i = 0; i < 32767 && bytesRead == -1; i++) {
		bytesRead = read(uartFd, receiveBuffer, receiveBufferSize);
	}

	if (bytesRead < 0) {
		Log_Debug("ERROR: Could not read UART: %s (%d).\n", strerror(errno), errno);
		terminationRequired = true;
		return;
	}
	receiveBuffer[bytesRead] = 0;

	do {
		//#if 0
		for (int i = 0; i < bytesRead; i++) {
			//battery or button
			if (b > 0 && receiveBuffer[i] == 'a') {
				battery = 1;
				b = 0;
			}
			if (recordbatteryvalue > 0 && receiveBuffer[i] != '}') {
				batteryvalue[batterystart] = receiveBuffer[i];
				batterystart++;
			}
			if (battery > 0 && receiveBuffer[i] == ':') {
				//start recording battery value
				recordbatteryvalue++;
			}

			if (recordbatteryvalue > 0 && receiveBuffer[i] == '}') {
				recordbatteryvalue = 0;
				batterystart = 0;
			}

			if (b > 0 && receiveBuffer[i] == 'u') {
				//determined button value
				//Log_Debug("WE GOT A BUTTON PRESS");
				button = 1;
				b = 0;
			}
			if (S > 0 && receiveBuffer[i] == 't') {
				door = 1;
				S = 0;
			}
			else {
				S = 0;
			}
			if (door == 1 && receiveBuffer[i] == '1') {
				buttondata[0] = '1';
			}
			if (door == 1 && receiveBuffer[i] == '0') {
				buttondata[0] = '0';
			}

			if (button == 1 && receiveBuffer[i] == '1') {
				buttondata[0] = '1';
			}
			if (button == 1 && receiveBuffer[i] == '0') {
				buttondata[0] = '0';
			}

			if (D > 0 && receiveBuffer[i] != '0')
				D = 0;
			if (D > 0 && receiveBuffer[i] == '0') {
				gotoname = true;
				D = 0;
			}
			if (namestart >= 4) {
				recordnamestart = false;
				for (int l = 0; l < sizeof(name2) - 1; l++) {
					name2[l] = name[l];
				}
				namestart = 0;

				memset(&name[0], 0, sizeof(name));
			}

			if (recordnamestart) {
				name[namestart] = receiveBuffer[i];
				namestart++;
			}

			if (gotoname && receiveBuffer[i] == '5') {
				recordnamestart = true;
				gotoname = false;
			}

			if (e > 0 && receiveBuffer[i] != 'V')
				e = 0;
			if (e > 0 && receiveBuffer[i] == 'V') {
				gotobracket = true;
				e = 0;
			}

			if (recordstart && receiveBuffer[i] == ']') {
				recordstart = false;
				for (int l = 0; l < sizeof(value2) - 1; l++) {
					value2[l] = value[l];
				}
				valuestart = 0;
				memset(&value[0], 0, sizeof(value));
			}
			if (recordstart) {
				value[valuestart] = receiveBuffer[i];
				valuestart++;
			}
			//EVALUE STARTS HERE
			if (receiveBuffer[i] == ',' && got1 == 1 && recordstart) {
				got2 = 1;
			}
			if (receiveBuffer[i] == ',' && got1 == 0 && recordstart) {
				got1 = 1;
			}
			if (got1 == 0 && got2 == 0 && recordstart && receiveBuffer[i] != ',') {
				if (evalue1start < 2) {
					evalue1[evalue1start] = receiveBuffer[i];
				}
				evalue1start++;
			}
			if (got1 == 1 && got2 == 0 && recordstart && receiveBuffer[i] != ',') {
				if (evalue2start < 2) {
					evalue2[evalue2start] = receiveBuffer[i];
				}
				evalue2start++;
			}
			if (got1 == 1 && got2 == 1 && recordstart && receiveBuffer[i] != ',') {
				if (evalue3start < 3) {
					evalue3[evalue3start] = receiveBuffer[i];
				}
				//evalue3[evalue3start] = receiveBuffer[i];
				evalue3start++;
			}
			//EVALUE ENDS HERE
			if (gotobracket && receiveBuffer[i] == '[') {
				//begin capturing evalue data
				recordstart = true;
				gotobracket = 0;
			}

			switch (receiveBuffer[i]) {
			case '{':
				matchleft++;
				messagestart = 0;
				message[messagestart] = receiveBuffer[i];
				messagestart++;
				break;
			case '}':
				matchright++;
				message[messagestart] = receiveBuffer[i];
				if (matchleft == matchright) {
					//complete message, print
					Log_Debug("my whole message is: %s \n", (char *)message);

					if (name2[3] == '8' && value2[0] != '0' && door == 1) {
						SendDoorState(buttondata); //mydoorstate
					}
					else if (name2[3] == '8' && value2[0] != '0' && battery == 1) {
						//Log_Debug("SENDING DOORBATTERY OF : %s\n", (char *)batteryvalue);
						SendDoorBattery(batteryvalue);//evalue1
					}

					else if (name2[3] == '8') {
						got1 = 0;
						got2 = 0;
						evalue1start = 0;
						evalue2start = 0;
						evalue3start = 0;

						memset(&value2[0], 0, sizeof(value2));
						memset(&name2[0], 0, sizeof(name2));
					}
					else if (name2[3] == '4' && value2[0] != '0' && battery == 0) {

						SendRoomTemperature(evalue1);
						SendRoomHumidity(evalue2);
						SendRoomPressure(evalue3);
					}
					else if (name2[3] == '3' && value2[0] != '0' && battery == 0) {
						//if node is from server cabinet
						SendServerTemperature(evalue1);
						SendServerHumidity(evalue2);
						SendServerPressure(evalue3);
					}
					else if (name2[3] == '6' && value2[0] != '0' && battery == 0) {

						SendOutsideTemperature(evalue1);
						SendOutsideHumidity(evalue2);
						SendOutsidePressure(evalue3);
					}
					else if (name2[3] == '6' && value2[0] != '0' && battery == 1) {
						SendOutsideBattery(batteryvalue);
					}
					else if (name2[3] == '3' && value2[0] != '0' && battery == 1) {
						SendServerBattery(batteryvalue);
					}
					else if (name2[3] == '4' && value2[0] != '0' && battery == 1) {
						SendRoomBattery(batteryvalue);
					}
					else if (name2[3] == '2' && value2[0] != '0' && battery == 1) {
						SendTrackerBattery(batteryvalue);
						SendInOffice(evalue1);
					}
					recordbatteryvalue = 0;
					batterystart = 0;
					S = 0;
					door = 0;
					battery = 0;
					button = 0;
					got1 = 0;
					got2 = 0;
					evalue1start = 0;
					evalue2start = 0;
					evalue3start = 0;

					memset(&batteryvalue[0], 0, sizeof(batteryvalue));

					memset(&value2[0], 0, sizeof(value2));
					memset(&name2[0], 0, sizeof(name2));

					memset(&message[0], 0, sizeof(message));
					messagestart = 0;
					matchleft = 0;
					matchright = 0;
					batterystart = 0;
				}
				break;
			case 'b':
				b++;
			case 'e':
				e++;
			case 'D':
				D++;
			case 'S':
				S++;
			default:
				message[messagestart] = receiveBuffer[i];
				messagestart++;
				break;
			}
		}
		//#endif
				//Log_Debug("%s", (char *)receiveBuffer);
	} while ((bytesRead = read(uartFd, receiveBuffer, receiveBufferSize)) > 0);
}



// event handler data structures. Only the event handler field needs to be populated.
static EventData buttonEventData = { .eventHandler = &ButtonTimerEventHandler };
static EventData uartEventData = { .eventHandler = &UartEventHandler };

//END OF UART SEGMENT


/// <summary>
/// Button timer event:  Check the status of buttons A and B
/// </summary>
static void ButtonPollTimerEventHandler(EventData *eventData)
{
	if (ConsumeTimerFdEvent(buttonPollTimerFd) != 0) {
		terminationRequired = true;
		return;
	}
	SendMessageButtonHandler();
	SendOrientationButtonHandler();
}

/// <summary>
/// Azure timer event:  Check connection status and send telemetry
/// </summary>
static void AzureTimerEventHandler(EventData *eventData)
{
	if (ConsumeTimerFdEvent(azureTimerFd) != 0) {
		terminationRequired = true;
		return;
	}

	bool isNetworkReady = false;
	if (Networking_IsNetworkingReady(&isNetworkReady) != -1) {
		if (isNetworkReady && !iothubAuthenticated) {
			SetupAzureClient();
		}
	}
	else {
		Log_Debug("Failed to get Network state\n");
	}

	if (iothubAuthenticated) {
		SendSimulatedTemperature();
		IoTHubDeviceClient_LL_DoWork(iothubClientHandle);
	}
}

// event handler data structures. Only the event handler field needs to be populated.
static EventData buttonPollEventData = { .eventHandler = &ButtonPollTimerEventHandler };
static EventData azureEventData = { .eventHandler = &AzureTimerEventHandler };

/// <summary>
///     Set up SIGTERM termination handler, initialize peripherals, and set up event handlers.
/// </summary>
/// <returns>0 on success, or -1 on failure</returns>
static int InitPeripheralsAndHandlers(void)
{
	struct sigaction action;
	memset(&action, 0, sizeof(struct sigaction));
	action.sa_handler = TerminationHandler;
	sigaction(SIGTERM, &action, NULL);

	epollFd = CreateEpollFd();
	if (epollFd < 0) {
		return -1;
	}

	UART_Config uartConfig;
	UART_InitConfig(&uartConfig);
	uartConfig.baudRate = 115200;
	uartConfig.flowControl = UART_FlowControl_None;
	uartFd = UART_Open(SAMPLE_UART, &uartConfig);
	if (uartFd < 0) {
		Log_Debug("ERROR: Could not open UART: %s (%d).\n", strerror(errno), errno);
		return -1;
	}
	if (RegisterEventHandlerToEpoll(epollFd, uartFd, &uartEventData, EPOLLIN) != 0) {
		return -1;
	}

	// Open button GPIO as input, and set up a timer to poll it

	Log_Debug("Opening SAMPLE_BUTTON_1 as input.\n");
	gpioButtonFd = GPIO_OpenAsInput(SAMPLE_BUTTON_1);
	if (gpioButtonFd < 0) {
		Log_Debug("ERROR: Could not open button GPIO: %s (%d).\n", strerror(errno), errno);
		return -1;
	}
	struct timespec buttonPressCheckPeriod = { 0, 1000000 };
	gpioButtonTimerFd =
		CreateTimerFdAndAddToEpoll(epollFd, &buttonPressCheckPeriod, &buttonEventData, EPOLLIN);
	if (gpioButtonTimerFd < 0) {
		return -1;
	}

	//END UART

	azureIoTPollPeriodSeconds = AzureIoTDefaultPollPeriodSeconds;
	struct timespec azureTelemetryPeriod = { azureIoTPollPeriodSeconds, 0 };
	azureTimerFd =
		CreateTimerFdAndAddToEpoll(epollFd, &azureTelemetryPeriod, &azureEventData, EPOLLIN);
	/*if (buttonPollTimerFd < 0) {
		Log_Debug("-1 RETURNED AT 380");
		return -1;
	}*/

	return 0;
}

/// <summary>
///     Close peripherals and handlers.
/// </summary>
static void ClosePeripheralsAndHandlers(void)
{
	Log_Debug("Closing file descriptors\n");

	// Leave the LEDs off
	if (deviceTwinStatusLedGpioFd >= 0) {
		GPIO_SetValue(deviceTwinStatusLedGpioFd, GPIO_Value_High);
	}
	CloseFdAndPrintError(buttonPollTimerFd, "ButtonTimer");
	CloseFdAndPrintError(azureTimerFd, "AzureTimer");
	CloseFdAndPrintError(sendMessageButtonGpioFd, "SendMessageButton");
	CloseFdAndPrintError(sendOrientationButtonGpioFd, "SendOrientationButton");
	CloseFdAndPrintError(deviceTwinStatusLedGpioFd, "StatusLed");
	CloseFdAndPrintError(gpioButtonFd, "GpioButton");
	CloseFdAndPrintError(uartFd, "Uart");
	CloseFdAndPrintError(epollFd, "Epoll");
}

/// <summary>
///     Sets the IoT Hub authentication state for the app
///     The SAS Token expires which will set the authentication state
/// </summary>
static void HubConnectionStatusCallback(IOTHUB_CLIENT_CONNECTION_STATUS result,
	IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason,
	void *userContextCallback)
{
	iothubAuthenticated = (result == IOTHUB_CLIENT_CONNECTION_AUTHENTICATED);
	Log_Debug("IoT Hub Authenticated: %s\n", GetReasonString(reason));
}

/// <summary>
///     Sets up the Azure IoT Hub connection (creates the iothubClientHandle)
///     When the SAS Token for a device expires the connection needs to be recreated
///     which is why this is not simply a one time call.
/// </summary>

char * EtherDATA_Message[100];

static void ReceiveHubMessage(IOTHUB_CLIENT_CONFIRMATION_RESULT result, const unsigned char *payload, size_t payloadSize, void *userContextCallback)
{
	size_t nullTerminatedJsonSize = payloadSize + 1;
	char *nullTerminatedJsonString = (char *)malloc(nullTerminatedJsonSize);
	if (nullTerminatedJsonString == NULL) {
		Log_Debug("ERROR: Could not allocate buffer for payload.\n");
		abort();
	}
	// Copy the provided buffer to a null terminated buffer.
	memcpy(nullTerminatedJsonString, payload, payloadSize);
	// Add the null terminator at the end.
	nullTerminatedJsonString[nullTerminatedJsonSize - 1] = 0;

	JSON_Value *rootProperties = NULL;
	rootProperties = json_parse_string(nullTerminatedJsonString);
	if (rootProperties == NULL) {
		Log_Debug("WARNING: Cannot parse the string as JSON content.\n");
		goto cleanup;
	}
	char a[20] = "";
	JSON_Object *rootObject = json_value_get_object(rootProperties);
	int y = 0;
	y = json_object_dotget_number(rootObject, "hub_code");
	Log_Debug("The Number sent from the Hub is %d", y);

	switch (y) {
	case 123:
		SendUartMessage(uartFd, "{\"cmd\":\"emIdentNodeByName\",\"args\":[\"A\"]}");
		Log_Debug("\ntried sending {\"cmd\":\"emIdentNodeByName\",\"args\":[\"A\"]} via uart\n"); //{"cmd":"emIdentNodeByName","args":["A"]}

		break;

	default:
		break;
	}

cleanup:
	// Release the allocated memory.
	json_value_free(rootProperties);
	free(nullTerminatedJsonString);
}

static void SetupAzureClient(void)
{
	if (iothubClientHandle != NULL)
		IoTHubDeviceClient_LL_Destroy(iothubClientHandle);

	AZURE_SPHERE_PROV_RETURN_VALUE provResult =
		IoTHubDeviceClient_LL_CreateWithAzureSphereDeviceAuthProvisioning(scopeId, 10000,
			&iothubClientHandle);
	Log_Debug("IoTHubDeviceClient_LL_CreateWithAzureSphereDeviceAuthProvisioning returned '%s'.\n",
		getAzureSphereProvisioningResultString(provResult));

	if (provResult.result != AZURE_SPHERE_PROV_RESULT_OK) {

		// If we fail to connect, reduce the polling frequency, starting at
		// AzureIoTMinReconnectPeriodSeconds and with a backoff up to
		// AzureIoTMaxReconnectPeriodSeconds
		if (azureIoTPollPeriodSeconds == AzureIoTDefaultPollPeriodSeconds) {
			azureIoTPollPeriodSeconds = AzureIoTMinReconnectPeriodSeconds;
		}
		else {
			azureIoTPollPeriodSeconds *= 2;
			if (azureIoTPollPeriodSeconds > AzureIoTMaxReconnectPeriodSeconds) {
				azureIoTPollPeriodSeconds = AzureIoTMaxReconnectPeriodSeconds;
			}
		}

		struct timespec azureTelemetryPeriod = { azureIoTPollPeriodSeconds, 0 };
		SetTimerFdToPeriod(azureTimerFd, &azureTelemetryPeriod);

		Log_Debug("ERROR: failure to create IoTHub Handle - will retry in %i seconds.\n",
			azureIoTPollPeriodSeconds);
		return;
	}

	// Successfully connected, so make sure the polling frequency is back to the default
	azureIoTPollPeriodSeconds = AzureIoTDefaultPollPeriodSeconds;
	struct timespec azureTelemetryPeriod = { azureIoTPollPeriodSeconds, 0 };
	SetTimerFdToPeriod(azureTimerFd, &azureTelemetryPeriod);

	iothubAuthenticated = true;

	if (IoTHubDeviceClient_LL_SetOption(iothubClientHandle, OPTION_KEEP_ALIVE,
		&keepalivePeriodSeconds) != IOTHUB_CLIENT_OK) {
		Log_Debug("ERROR: failure setting option \"%s\"\n", OPTION_KEEP_ALIVE);
		return;
	}

	IoTHubDeviceClient_LL_SetDeviceMethodCallback(iothubClientHandle, ReceiveHubMessage, NULL);
	//IoTHubDeviceClient_LL_DeviceMethodResponse(iothubClientHandle, HubConnectionStatusCallback, NULL, 1, 1);

	IoTHubDeviceClient_LL_SetDeviceTwinCallback(iothubClientHandle, TwinCallback, NULL);
	IoTHubDeviceClient_LL_SetConnectionStatusCallback(iothubClientHandle,
		HubConnectionStatusCallback, NULL);
}


/// <summary>
///     Callback invoked when a Device Twin update is received from IoT Hub.
///     Updates local state for 'showEvents' (bool).
/// </summary>
/// <param name="payload">contains the Device Twin JSON document (desired and reported)</param>
/// <param name="payloadSize">size of the Device Twin JSON document</param>
static void TwinCallback(DEVICE_TWIN_UPDATE_STATE updateState, const unsigned char *payload,
	size_t payloadSize, void *userContextCallback)
{
	size_t nullTerminatedJsonSize = payloadSize + 1;
	char *nullTerminatedJsonString = (char *)malloc(nullTerminatedJsonSize);
	if (nullTerminatedJsonString == NULL) {
		Log_Debug("ERROR: Could not allocate buffer for twin update payload.\n");
		abort();
	}
	// Copy the provided buffer to a null terminated buffer.
	memcpy(nullTerminatedJsonString, payload, payloadSize);
	// Add the null terminator at the end.
	nullTerminatedJsonString[nullTerminatedJsonSize - 1] = 0;

	JSON_Value *rootProperties = NULL;
	rootProperties = json_parse_string(nullTerminatedJsonString);
	if (rootProperties == NULL) {
		Log_Debug("WARNING: Cannot parse the string as JSON content.\n");
		goto cleanup;
	}

	JSON_Object *rootObject = json_value_get_object(rootProperties);
	JSON_Object *desiredProperties = json_object_dotget_object(rootObject, "desired");
	if (desiredProperties == NULL) {
		desiredProperties = rootObject;
	}

	// Handle the Device Twin Desired Properties here.
	JSON_Object *LEDState = json_object_dotget_object(desiredProperties, "StatusLED");
	if (LEDState != NULL) {
		statusLedOn = (bool)json_object_get_boolean(LEDState, "value");
		GPIO_SetValue(deviceTwinStatusLedGpioFd,
			(statusLedOn == true ? GPIO_Value_Low : GPIO_Value_High));
		TwinReportBoolState("StatusLED", statusLedOn);
	}

	JSON_Object *HUBState = json_object_dotget_object(desiredProperties, "office_LED");
	if (HUBState != NULL) {
		char hub_code[10] = "";
		office_LED = (bool)json_object_get_boolean(HUBState, "value");
		//Log_Debug("WE GRABBED HUB_CODE WITH VALUE: %s\n", (bool)office_LED);

		TwinReportBoolState("OFFICE LED", office_LED);
	}

	JSON_Object *HUBState2 = json_object_dotget_object(desiredProperties, "server_LED");
	if (HUBState2 != NULL) {
		char hub_code[10] = "";
		server_LED = (bool)json_object_get_boolean(HUBState2, "value");
		//Log_Debug("WE GRABBED HUB_CODE WITH VALUE: %s\n", (bool)office_LED);

		TwinReportBoolState("SERVER LED", server_LED);
	}

	JSON_Object *HUBState3 = json_object_dotget_object(desiredProperties, "outside_LED");
	if (HUBState3 != NULL) {
		char hub_code[10] = "";
		outside_LED = (bool)json_object_get_boolean(HUBState3, "value");
		//Log_Debug("WE GRABBED HUB_CODE WITH VALUE: %s\n", (bool)office_LED);

		TwinReportBoolState("OUTSIDE LED", outside_LED);
	}
	JSON_Object *HUBState4 = json_object_dotget_object(desiredProperties, "tracker_LED");
	if (HUBState4 != NULL) {
		char hub_code[10] = "";
		tracker_LED = (bool)json_object_get_boolean(HUBState4, "value");
		//Log_Debug("WE GRABBED HUB_CODE WITH VALUE: %s\n", (bool)office_LED);

		TwinReportBoolState("TRACKER LED", tracker_LED);
	}

cleanup:
	// Release the allocated memory.
	json_value_free(rootProperties);
	free(nullTerminatedJsonString);
}

/// <summary>
///     Converts the IoT Hub connection status reason to a string.
/// </summary>
static const char *GetReasonString(IOTHUB_CLIENT_CONNECTION_STATUS_REASON reason)
{
	static char *reasonString = "unknown reason";
	switch (reason) {
	case IOTHUB_CLIENT_CONNECTION_EXPIRED_SAS_TOKEN:
		reasonString = "IOTHUB_CLIENT_CONNECTION_EXPIRED_SAS_TOKEN";
		break;
	case IOTHUB_CLIENT_CONNECTION_DEVICE_DISABLED:
		reasonString = "IOTHUB_CLIENT_CONNECTION_DEVICE_DISABLED";
		break;
	case IOTHUB_CLIENT_CONNECTION_BAD_CREDENTIAL:
		reasonString = "IOTHUB_CLIENT_CONNECTION_BAD_CREDENTIAL";
		break;
	case IOTHUB_CLIENT_CONNECTION_RETRY_EXPIRED:
		reasonString = "IOTHUB_CLIENT_CONNECTION_RETRY_EXPIRED";
		break;
	case IOTHUB_CLIENT_CONNECTION_NO_NETWORK:
		reasonString = "IOTHUB_CLIENT_CONNECTION_NO_NETWORK";
		break;
	case IOTHUB_CLIENT_CONNECTION_COMMUNICATION_ERROR:
		reasonString = "IOTHUB_CLIENT_CONNECTION_COMMUNICATION_ERROR";
		break;
	case IOTHUB_CLIENT_CONNECTION_OK:
		reasonString = "IOTHUB_CLIENT_CONNECTION_OK";
		break;
	}
	return reasonString;
}

/// <summary>
///     Converts AZURE_SPHERE_PROV_RETURN_VALUE to a string.
/// </summary>
static const char *getAzureSphereProvisioningResultString(
	AZURE_SPHERE_PROV_RETURN_VALUE provisioningResult)
{
	switch (provisioningResult.result) {
	case AZURE_SPHERE_PROV_RESULT_OK:
		return "AZURE_SPHERE_PROV_RESULT_OK";
	case AZURE_SPHERE_PROV_RESULT_INVALID_PARAM:
		return "AZURE_SPHERE_PROV_RESULT_INVALID_PARAM";
	case AZURE_SPHERE_PROV_RESULT_NETWORK_NOT_READY:
		return "AZURE_SPHERE_PROV_RESULT_NETWORK_NOT_READY";
	case AZURE_SPHERE_PROV_RESULT_DEVICEAUTH_NOT_READY:
		return "AZURE_SPHERE_PROV_RESULT_DEVICEAUTH_NOT_READY";
	case AZURE_SPHERE_PROV_RESULT_PROV_DEVICE_ERROR:
		return "AZURE_SPHERE_PROV_RESULT_PROV_DEVICE_ERROR";
	case AZURE_SPHERE_PROV_RESULT_GENERIC_ERROR:
		return "AZURE_SPHERE_PROV_RESULT_GENERIC_ERROR";
	default:
		return "UNKNOWN_RETURN_VALUE";
	}
}

/// <summary>
///     Sends telemetry to IoT Hub
/// </summary>
/// <param name="key">The telemetry item to update</param>
/// <param name="value">new telemetry value</param>



static void SendDoorState(const unsigned char *value)
{
	//Log_Debug("MY CHOPPED UP ROOMTEMP IS: %s%s%s%s", (char *)value1, (char *)value2, (char *)value3, (char *)value4);
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"DoorState\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	//int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;

	//Log_Debug("Sending IoT Hub Message: %s\n", eventBuffer);

	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		//	Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendInOffice(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"inOffice\": \"1\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate);
	//int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;
	//Log_Debug("Sending IoT Hub Message: %s\n", eventBuffer);
	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		//	Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendDoorBattery(const unsigned char *value)
{
	//Log_Debug("MY CHOPPED UP ROOMTEMP IS: %s%s%s%s", (char *)value1, (char *)value2, (char *)value3, (char *)value4);
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"DoorBat\": \"%s\"}";
	//int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate);
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;

	//Log_Debug("Sending IoT Hub Message: %s\n", eventBuffer);

	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		//	Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendTrackerBattery(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"TrackerBat\": \"%s\"}";
	//int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate);
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;

	//Log_Debug("Sending IoT Hub Message: %s\n", eventBuffer);

	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		//	Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendOutsideBattery(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"OutsideBat\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;


	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
			Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendServerBattery(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"ServerBat\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;


	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendRoomBattery(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"RoomBat\": \"%s\"}";
	//int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate);
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;


	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		//	Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}


static void SendOutsidePressure(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"OutsidePres\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;


	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendServerPressure(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"ServerPres\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;


	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendRoomPressure(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"RoomPres\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;


	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		//	Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendOutsideHumidity(const unsigned char *value)
{

	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"OutsideHumi\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;

	//Log_Debug("Sending IoT Hub Message: %s\n", eventBuffer);

	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendServerHumidity(const unsigned char *value)
{

	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"ServerHumi\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;


	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
	}

	IoTHubMessage_Destroy(messageHandle);
}
static void SendRoomHumidity(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"RoomHumi\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	//int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;

	//Log_Debug("Sending IoT Hub Message: %s\n", eventBuffer);

	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		//Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendOutsideTemperature(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"OutsideTemp\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	//int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;

	//Log_Debug("Sending IoT Hub Message: %s\n", eventBuffer);

	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		//Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendServerTemperature(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"ServerTemp\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	//int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;

	//Log_Debug("Sending IoT Hub Message: %s\n", eventBuffer);

	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		//Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendRoomTemperature(const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"RoomTemp\": \"%s\"}";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	//int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, value);
	if (len < 0)
		return;


	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		//Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}

static void SendTelemetry(const unsigned char *key, const unsigned char *value)
{
	static char eventBuffer[100] = { 0 };
	static const char *EventMsgTemplate = "{ \"Name\": \"%s\", \"Evalue\": \"%s\" }";
	int len = snprintf(eventBuffer, sizeof(eventBuffer), EventMsgTemplate, key, value);
	if (len < 0)
		return;

	//Log_Debug("Sending IoT Hub Message: %s\n", eventBuffer);

	IOTHUB_MESSAGE_HANDLE messageHandle = IoTHubMessage_CreateFromString(eventBuffer);

	if (messageHandle == 0) {
		Log_Debug("WARNING: unable to create a new IoTHubMessage\n");
		return;
	}

	if (IoTHubDeviceClient_LL_SendEventAsync(iothubClientHandle, messageHandle, SendMessageCallback,
		/*&callback_param*/ 0) != IOTHUB_CLIENT_OK) {
		Log_Debug("WARNING: failed to hand over the message to IoTHubClient\n");
	}
	else {
		//	Log_Debug("INFO: IoTHubClient accepted the message for delivery\n");
	}

	IoTHubMessage_Destroy(messageHandle);
}

/// <summary>
///     Callback confirming message delivered to IoT Hub.
/// </summary>
/// <param name="result">Message delivery status</param>
/// <param name="context">User specified context</param>
static void SendMessageCallback(IOTHUB_CLIENT_CONFIRMATION_RESULT result, void *context)
{
	//Log_Debug("INFO: Message received by IoT Hub. Result is: %d\n", result);
}

/// <summary>
///     Creates and enqueues a report containing the name and value pair of a Device Twin reported
///     property. The report is not sent immediately, but it is sent on the next invocation of
///     IoTHubDeviceClient_LL_DoWork().
/// </summary>
/// <param name="propertyName">the IoT Hub Device Twin property name</param>
/// <param name="propertyValue">the IoT Hub Device Twin property value</param>
static void TwinReportBoolState(const char *propertyName, bool propertyValue)
{
	if (iothubClientHandle == NULL) {
		Log_Debug("ERROR: client not initialized\n");
	}
	else {
		static char reportedPropertiesString[30] = { 0 };
		int len = snprintf(reportedPropertiesString, 30, "{\"%s\":%s}", propertyName,
			(propertyValue == true ? "true" : "false"));
		if (len < 0)
			return;

		if (IoTHubDeviceClient_LL_SendReportedState(
			iothubClientHandle, (unsigned char *)reportedPropertiesString,
			strlen(reportedPropertiesString), ReportStatusCallback, 0) != IOTHUB_CLIENT_OK) {
			Log_Debug("ERROR: failed to set reported state for '%s'.\n", propertyName);
		}
		else {
			Log_Debug("INFO: Reported state for '%s' to value '%s'.\n", propertyName,
				(propertyValue == true ? "true" : "false"));
		}
	}
}

/// <summary>
///     Callback invoked when the Device Twin reported properties are accepted by IoT Hub.
/// </summary>
static void ReportStatusCallback(int result, void *context)
{
	Log_Debug("INFO: Device Twin reported properties update result: HTTP status code %d\n", result);
}

/// <summary>
///     Generates a simulated Temperature and sends to IoT Hub.
/// </summary>
void SendSimulatedTemperature(void)
{
	static float temperature = 30.0;
	float deltaTemp = (float)(rand() % 20) / 20.0f;
	if (rand() % 2 == 0) {
		temperature += deltaTemp;
	}
	else {
		temperature -= deltaTemp;
	}

	char tempBuffer[20];
	int len = snprintf(tempBuffer, 20, "%3.2f", temperature);
	//if (len > 0)
	   // SendTelemetry("Temperature", tempBuffer);
}

/// <summary>
///     Check whether a given button has just been pressed.
/// </summary>
/// <param name="fd">The button file descriptor</param>
/// <param name="oldState">Old state of the button (pressed or released)</param>
/// <returns>true if pressed, false otherwise</returns>
static bool IsButtonPressed(int fd, GPIO_Value_Type *oldState)
{
	bool isButtonPressed = false;
	GPIO_Value_Type newState;
	int result = GPIO_GetValue(fd, &newState);
	if (result != 0) {
		Log_Debug("ERROR: Could not read button GPIO: %s (%d).\n", strerror(errno), errno);
		terminationRequired = true;
	}
	else {
		// Button is pressed if it is low and different than last known state.
		isButtonPressed = (newState != *oldState) && (newState == GPIO_Value_Low);
		*oldState = newState;
	}

	return isButtonPressed;
}

/// <summary>
/// Pressing button A will:
///     Send a 'Button Pressed' event to Azure IoT Central
/// </summary>
static void SendMessageButtonHandler(void)
{
	if (IsButtonPressed(sendMessageButtonGpioFd, &sendMessageButtonState)) {
		SendTelemetry("ButtonPress", "True");
	}
}

/// <summary>
/// Pressing button B will:
///     Send an 'Orientation' event to Azure IoT Central
/// </summary>
static void SendOrientationButtonHandler(void)
{
	if (IsButtonPressed(sendOrientationButtonGpioFd, &sendOrientationButtonState)) {
		deviceIsUp = !deviceIsUp;
		SendTelemetry("Orientation", deviceIsUp ? "Up" : "Down");
	}
}


