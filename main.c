//*****************************************************************************
//
// Application Name     - gpio-interrupt-example
// Application Overview - The objective of this application is to demonstrate
//                          GPIO interrupts using SW2 and SW3.
//                          NOTE: the switches are not debounced!
//
//*****************************************************************************


// Standard includes
//#include <pin_mux_config.h>
#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <stdlib.h>
#include <math.h>
#include <time.h>

// Driverlib includes
#include "hw_types.h"
#include "hw_ints.h"
#include "hw_memmap.h"
#include "hw_nvic.h"
#include "hw_common_reg.h"
#include "interrupt.h"
#include "hw_apps_rcm.h"
#include "prcm.h"
#include "rom.h"
#include "spi.h"
#include "rom_map.h"
#include "prcm.h"
#include "gpio.h"
#include "utils.h"
#include "systick.h"
#include "rom_map.h"
#include "uart.h"
#include "i2c_if.h"
#include "timer.h"
#include "timer_if.h"
#include "simplelink.h"


// Common interface includes
#include "uart_if.h"
#include "Adafruit_GFX.h"
#include "pin_mux_config.h"
#include "Adafruit_SSD1351.h"
#include "oled_test.h"
#include "glcdfont.h"
#include "utils/network_utils.h"



#define APPLICATION_VERSION     "1.4.0"
#define APP_NAME                "I2C Demo"
#define UART_PRINT              Report
#define FOREVER                 1
#define CONSOLE                 UARTA0_BASE
#define FAILURE                 -1
#define SUCCESS                 0
#define RETERR_IF_TRUE(condition) {if(condition) return FAILURE;}
#define RET_IF_ERR(Func)          {int iRetVal = (Func); \
                                   if (SUCCESS != iRetVal) \
                                     return  iRetVal;}
#define MASTER_MODE      1

#define SPI_IF_BIT_RATE  100000
#define TR_BUFF_SIZE     100

#define MASTER_MSG       "This is CC3200 SPI Master Application\n\r"
#define SLAVE_MSG        "This is CC3200 SPI Slave Application\n\r"

// AWS MACROS
//NEED TO UPDATE THIS FOR IT TO WORK!
#define DATE                6     /* Current Date */
#define MONTH               6     /* Month 1-12 */
#define YEAR                2024  /* Current year */
#define HOUR                14    /* Time - hours */
#define MINUTE              38    /* Time - minutes */
#define SECOND              0     /* Time - seconds */


#define APPLICATION_NAME      "SSL"
#define APPLICATION_VERSION   "SQ24"
#define SERVER_NAME           "a4w45g3ohtzb4-ats.iot.us-east-1.amazonaws.com" // CHANGE ME
#define GOOGLE_DST_PORT       8443


// Set the AWS macros
#define POSTHEADER "POST /things/Lana_CC3200_Board/shadow HTTP/1.1\r\n"             // CHANGE ME
#define HOSTHEADER "Host: a4w45g3ohtzb4-ats.iot.us-east-1.amazonaws.com\r\n"  // CHANGE ME
#define CHEADER "Connection: Keep-Alive\r\n"
#define CTHEADER "Content-Type: application/json; charset=utf-8\r\n"
#define CLHEADER1 "Content-Length: "
#define CLHEADER2 "\r\n\r\n"
#define GETHEADER "GET /things/Lana_CC3200_Board/shadow HTTP/1.1\r\n"

//*****************************************************************************
//                 GLOBAL VARIABLES -- Start
//*****************************************************************************
static unsigned char g_ucTxBuff[TR_BUFF_SIZE];
static unsigned char g_ucRxBuff[TR_BUFF_SIZE];
static unsigned char ucTxBuffNdx;
static unsigned char ucRxBuffNdx;

#if defined(ccs)
extern void (* const g_pfnVectors[])(void);
#endif
#if defined(ewarm)
extern uVectorEntry __vector_table;
#endif

extern void (* const g_pfnVectors[])(void);

//Switch buttons
typedef struct PinSetting {
    unsigned long port;
    unsigned int pin;
} PinSetting;

volatile unsigned long SW3_intcount;
volatile unsigned char SW3_intflag;

volatile unsigned long SW2_intcount;
volatile unsigned char SW2_intflag;

static const PinSetting switch3 = { .port = GPIOA1_BASE, .pin = 0x20};
static const PinSetting switch2 = { .port = GPIOA2_BASE, .pin = 0x40};

// IR Receiver
volatile unsigned long ir_intcount;
volatile unsigned long ir_intflag = 0;

// General timer
volatile int timer_flag;
unsigned long g_ulTimerInts;

// Systick timer
volatile uint64_t delta;
volatile uint64_t delta_us;

bool print = false;
volatile bool uartFlag = false;
volatile int canShootFlag = 0;

// Player life tracking
volatile int p1LifeCnt = 5;
volatile int p2LifeCnt = 5;
volatile int playerScore;
int maxLifeNum = 5;


// For AWS
char stored[1024];

int x = 0; // Tracks the current x-coordinate we are at
int y = 0; // Tracks the current y-coordinate we are at

// some helpful macros for systick

// the cc3200's fixed clock frequency of 80 MHz
// note the use of ULL to indicate an unsigned long long constant
#define SYSCLKFREQ 80000000ULL

// macro to convert ticks to microseconds
#define TICKS_TO_US(ticks) \
    ((((ticks) / SYSCLKFREQ) * 1000000ULL) + \
    ((((ticks) % SYSCLKFREQ) * 1000000ULL) / SYSCLKFREQ))\

// macro to convert microseconds to ticks
#define US_TO_TICKS(us) ((SYSCLKFREQ / 1000000ULL) * (us))

// systick reload value set to 40ms period
// (PERIOD_SEC) * (SYSCLKFREQ) = PERIOD_TICKS
#define SYSTICK_RELOAD_VAL 3200000UL

// track systick counter periods elapsed
// if it is not 0, we know the transmission ended
volatile int systick_cnt = 0;
volatile int timeout = 0;

extern void (* const g_pfnVectors[])(void);
static uint8_t buffer[1024];
volatile uint16_t buffIndex = 0;
volatile bool startNewBitRd;
static uint8_t buffer[1024];

static volatile unsigned long g_ulBase;

volatile uint16_t strStackIndex = 0;

char *OledString = "";

static const PinSetting ir = { .port = GPIOA0_BASE, .pin = 0x1};

static int set_time();
static void BoardInit(void);

/**
 * Reset SysTick Counter
 */
static inline void SysTickReset(void) {
    // any write to the ST_CURRENT register clears it
    // after clearing it automatically gets reset without
    // triggering exception logic
    // see reference manual section 3.2.1
    HWREG(NVIC_ST_CURRENT) = 1;

    // clear the global count variable
    systick_cnt = 0;
   // timeout = 0;
}


// SW3 Button Handler
static void GPIOA2IntHandler(void) {
    unsigned long ulStatus;
    Report("SW Pressed! \r\n");

    ulStatus = MAP_GPIOIntStatus (switch3.port, true);
    MAP_GPIOIntClear(switch3.port, ulStatus);       // clear interrupts on GPIOA2
    SW3_intcount++;
    SW3_intflag=1;
}

// SW2 Button Handler
static void GPIOA1IntHandler(void) {
    unsigned long ulStatus;
    Report("SW2 Pressed! \r\n");

    ulStatus = MAP_GPIOIntStatus (switch2.port, true);
    MAP_GPIOIntClear(switch2.port, ulStatus);       // clear interrupts on GPIOA2
    SW2_intcount++;
    SW2_intflag=1;
}

// For the remote and IR receiver
static void GPIOIrHandler(void) {
    unsigned long ulStatus;

    ulStatus = MAP_GPIOIntStatus (ir.port, true);
    MAP_GPIOIntClear(ir.port, ulStatus);       // clear interrupts on GPIOA2

    // Calculate the delta
    delta = SYSTICK_RELOAD_VAL - SysTickValueGet();
    delta_us = TICKS_TO_US(delta); // convert elapsed cycles to microseconds

    if(13400 < delta_us && delta_us < 14000) {
        startNewBitRd = 1;
        buffIndex = 0;
    } else if(buffIndex == 32) {
        buffIndex = 0;
        startNewBitRd = false;
    } else if(1000 < delta_us && delta_us < 1300 && startNewBitRd ) {
        buffer[buffIndex] = '0';
        buffIndex++;
    } else if (2000 < delta_us && delta_us < 2700 && startNewBitRd) {
        buffer[buffIndex] = '1';
        buffIndex++;
    }

    ir_intcount++;
    ir_intflag=1;
    SysTickReset();
}


/**
 * SysTick Interrupt Handler
 * Keep track of whether the systick counter wrapped
 */
static void SysTickHandler(void) {
    // increment every time the systick handler fires
    systick_cnt++;
    timeout++;
}


/**
 * Initializes SysTick Module
 */
static void SysTickInit(void) {

    // configure the reset value for the systick countdown register
    MAP_SysTickPeriodSet(SYSTICK_RELOAD_VAL);

    // register interrupts on the systick module
    MAP_SysTickIntRegister(SysTickHandler);

    // enable interrupts on systick
    // (trigger SysTickHandler when countdown reaches 0)
    MAP_SysTickIntEnable();

    // enable the systick module itself
    MAP_SysTickEnable();
}

// The interrupt handler for the timer interrupt - controls consistency of OLED display
void TimerBaseIntHandler(void)
{
    // Clear the timer interrupt.
    Timer_IF_InterruptClear(g_ulBase);

    g_ulTimerInts ++;
    timer_flag = 1;
}


void DisplayBuffer(unsigned char *pucDataBuf, unsigned char ucLen)
{
    unsigned char ucBufIndx = 0;
    UART_PRINT("Read contents");
    UART_PRINT("\n\r");
    while(ucBufIndx < ucLen)
    {
        UART_PRINT(" 0x%x, ", pucDataBuf[ucBufIndx]);
        ucBufIndx++;
        if((ucBufIndx % 8) == 0)
        {
            UART_PRINT("\n\r");
        }
    }
    UART_PRINT("\n\r");
}

void UARTHandler() {
    //clear status of uart
    unsigned long ulUARTStatus = MAP_UARTIntStatus(UARTA1_BASE, true);
    UARTIntClear(UARTA1_BASE, ulUARTStatus);
    uartFlag = true;
}


static void SlaveIntHandler() {
    unsigned long ulRecvData;
    unsigned long ulStatus;

    ulStatus = MAP_SPIIntStatus(GSPI_BASE,true);

    MAP_SPIIntClear(GSPI_BASE,SPI_INT_RX_FULL|SPI_INT_TX_EMPTY);

    if(ulStatus & SPI_INT_TX_EMPTY)
    {
        MAP_SPIDataPut(GSPI_BASE,g_ucTxBuff[ucTxBuffNdx%TR_BUFF_SIZE]);
        ucTxBuffNdx++;
    }

    if(ulStatus & SPI_INT_RX_FULL)
    {
        MAP_SPIDataGetNonBlocking(GSPI_BASE,&ulRecvData);
        g_ucTxBuff[ucRxBuffNdx%TR_BUFF_SIZE] = ulRecvData;
        Report("%c",ulRecvData);
        ucRxBuffNdx++;
    }
}


void MasterMain() {
    unsigned long ulUserData;
    unsigned long ulDummy;

    // Initialize the message
    memcpy(g_ucTxBuff,MASTER_MSG,sizeof(MASTER_MSG));


    // Reset SPI
    MAP_SPIReset(GSPI_BASE);

    // Configure SPI interface
    MAP_SPIConfigSetExpClk(GSPI_BASE,MAP_PRCMPeripheralClockGet(PRCM_GSPI),
                     SPI_IF_BIT_RATE,SPI_MODE_MASTER,SPI_SUB_MODE_0,
                     (SPI_SW_CTRL_CS |
                     SPI_4PIN_MODE |
                     SPI_TURBO_OFF |
                     SPI_CS_ACTIVEHIGH |
                     SPI_WL_8));

    // Enable SPI for communication
    MAP_SPIEnable(GSPI_BASE);
}


void SlaveMain() {
    // Initialize the message
    memcpy(g_ucTxBuff,SLAVE_MSG,sizeof(SLAVE_MSG));

    // Set Tx buffer index
    ucTxBuffNdx = 0;
    ucRxBuffNdx = 0;

    // Reset SPI
    MAP_SPIReset(GSPI_BASE);

    // Configure SPI interface
    MAP_SPIConfigSetExpClk(GSPI_BASE,MAP_PRCMPeripheralClockGet(PRCM_GSPI),
                     SPI_IF_BIT_RATE,SPI_MODE_SLAVE,SPI_SUB_MODE_0,
                     (SPI_HW_CTRL_CS |
                     SPI_4PIN_MODE |
                     SPI_TURBO_OFF |
                     SPI_CS_ACTIVEHIGH |
                     SPI_WL_8));

    // Register Interrupt Handler
    MAP_SPIIntRegister(GSPI_BASE,SlaveIntHandler);

    // Enable Interrupts
    MAP_SPIIntEnable(GSPI_BASE,SPI_INT_RX_FULL|SPI_INT_TX_EMPTY);

    // Enable SPI for communication
    MAP_SPIEnable(GSPI_BASE);

    // Print mode on uart
    Message("Enabled SPI Interface in Slave Mode\n\rReceived : ");
}


static void
DisplayBanner(char * AppName)
{
    Report("\n\n\n\r");
    Report("\t\t *************************************************\n\r");
    Report("\t\t      CC3200 %s Application       \n\r", AppName);
    Report("\t\t *************************************************\n\r");
    Report("\n\n\n\r");
}


void
DisplayUsage()
{
    UART_PRINT("Command Usage \n\r");
    UART_PRINT("------------- \n\r");
    UART_PRINT("write <dev_addr> <wrlen> <<byte0> [<byte1> ... ]> <stop>\n\r");
    UART_PRINT("\t - Write data to the specified i2c device\n\r");
    UART_PRINT("read  <dev_addr> <rdlen> \n\r\t - Read data frpm the specified "
                "i2c device\n\r");
    UART_PRINT("writereg <dev_addr> <reg_offset> <wrlen> <<byte0> [<byte1> ... "
                "]> \n\r");
    UART_PRINT("\t - Write data to the specified register of the i2c device\n\r");
    UART_PRINT("readreg <dev_addr> <reg_offset> <rdlen> \n\r");
    UART_PRINT("\t - Read data from the specified register of the i2c device\n\r");
    UART_PRINT("\n\r");
    UART_PRINT("Parameters \n\r");
    UART_PRINT("---------- \n\r");
    UART_PRINT("dev_addr - slave address of the i2c device, a hex value "
                "preceeded by '0x'\n\r");
    UART_PRINT("reg_offset - register address in the i2c device, a hex value "
                "preceeded by '0x'\n\r");
    UART_PRINT("wrlen - number of bytes to be written, a decimal value \n\r");
    UART_PRINT("rdlen - number of bytes to be read, a decimal value \n\r");
    UART_PRINT("bytex - value of the data to be written, a hex value preceeded "
                "by '0x'\n\r");
    UART_PRINT("stop - number of stop bits, 0 or 1\n\r");
    UART_PRINT("--------------------------------------------------------------"
                "--------------- \n\r\n\r");

}


int
ProcessReadRegCommand(char *pcInpString)
{
    unsigned char ucDevAddr, ucRegOffset, ucRdLen;
    unsigned char aucRdDataBuf[256];
    char *pcErrPtr;

    //
    // Get the device address
    //
    pcInpString = strtok(NULL, " ");
    RETERR_IF_TRUE(pcInpString == NULL);
    ucDevAddr = (unsigned char)strtoul(pcInpString+2, &pcErrPtr, 16);
    //
    // Get the register offset address
    //
    pcInpString = strtok(NULL, " ");
    RETERR_IF_TRUE(pcInpString == NULL);
    ucRegOffset = (unsigned char)strtoul(pcInpString+2, &pcErrPtr, 16);

    //
    // Get the length of data to be read
    //
    pcInpString = strtok(NULL, " ");
    RETERR_IF_TRUE(pcInpString == NULL);
    ucRdLen = (unsigned char)strtoul(pcInpString, &pcErrPtr, 10);
    //RETERR_IF_TRUE(ucLen > sizeof(aucDataBuf));

    //
    // Write the register address to be read from.
    // Stop bit implicitly assumed to be 0.
    //
    RET_IF_ERR(I2C_IF_Write(ucDevAddr,&ucRegOffset,1,0));

    //
    // Read the specified length of data
    //
    RET_IF_ERR(I2C_IF_Read(ucDevAddr, &aucRdDataBuf[0], ucRdLen));

    UART_PRINT("I2C Read From address complete\n\r");

    //
    // Display the buffer over UART on successful readreg
    //
    DisplayBuffer(aucRdDataBuf, ucRdLen);

    return SUCCESS;
}


void
DisplayPrompt()
{
    UART_PRINT("\n\rcmd#");
}


int ProcessWriteCommand(char *pcInpString)
{
    unsigned char ucDevAddr, ucStopBit, ucLen;
    unsigned char aucDataBuf[256];
    char *pcErrPtr;
    int iRetVal, iLoopCnt;

    // Get the device address
    pcInpString = strtok(NULL, " ");
    RETERR_IF_TRUE(pcInpString == NULL);
    ucDevAddr = (unsigned char)strtoul(pcInpString+2, &pcErrPtr, 16);

    // Get the length of data to be written
    pcInpString = strtok(NULL, " ");
    RETERR_IF_TRUE(pcInpString == NULL);
    ucLen = (unsigned char)strtoul(pcInpString, &pcErrPtr, 10);
    //RETERR_IF_TRUE(ucLen > sizeof(aucDataBuf));

    for(iLoopCnt = 0; iLoopCnt < ucLen; iLoopCnt++)
    {
        // Store the data to be written
        pcInpString = strtok(NULL, " ");
        RETERR_IF_TRUE(pcInpString == NULL);
        aucDataBuf[iLoopCnt] =
                (unsigned char)strtoul(pcInpString+2, &pcErrPtr, 16);
    }

    // Get the stop bit
    pcInpString = strtok(NULL, " ");
    RETERR_IF_TRUE(pcInpString == NULL);
    ucStopBit = (unsigned char)strtoul(pcInpString, &pcErrPtr, 10);

    // Write the data to the specified address
    iRetVal = I2C_IF_Write(ucDevAddr, aucDataBuf, ucLen, ucStopBit);
    if(iRetVal == SUCCESS)
    {
        UART_PRINT("I2C Write complete\n\r");
    }
    else
    {
        UART_PRINT("I2C Write failed\n\r");
        return FAILURE;
    }

    return SUCCESS;
}

static void BoardInit(void) {
    /* In case of TI-RTOS vector table is initialize by OS itself */
    #ifndef USE_TIRTOS

      // Set vector table base
    #if defined(ccs)
        MAP_IntVTableBaseSet((unsigned long)&g_pfnVectors[0]);
    #endif
    #if defined(ewarm)
        MAP_IntVTableBaseSet((unsigned long)&__vector_table);
    #endif
    #endif

        // Enable Processor
        MAP_IntMasterEnable();
        MAP_IntEnable(FAULT_SYSTICK);

        PRCMCC3200MCUInit();

    MAP_IntVTableBaseSet((unsigned long)&g_pfnVectors[0]);

    // Enable Processor
    MAP_IntMasterEnable();
    MAP_IntEnable(FAULT_SYSTICK);

    PRCMCC3200MCUInit();
}


int ProcessReadCommand(char *pcInpString) {
    unsigned char ucDevAddr, ucLen;
    unsigned char aucDataBuf[256];
    char *pcErrPtr;
    int iRetVal;

    // Get the device address
    pcInpString = strtok(NULL, " ");
    RETERR_IF_TRUE(pcInpString == NULL);
    ucDevAddr = (unsigned char)strtoul(pcInpString+2, &pcErrPtr, 16);

    // Get the length of data to be read
    pcInpString = strtok(NULL, " ");
    RETERR_IF_TRUE(pcInpString == NULL);
    ucLen = (unsigned char)strtoul(pcInpString, &pcErrPtr, 10);
    //RETERR_IF_TRUE(ucLen > sizeof(aucDataBuf));

    // Read the specified length of data
    iRetVal = I2C_IF_Read(ucDevAddr, aucDataBuf, ucLen);

    if(iRetVal == SUCCESS)
    {
        UART_PRINT("I2C Read complete\n\r");

        // Display the buffer over UART on successful write
        DisplayBuffer(aucDataBuf, ucLen);
    } else
    {
        UART_PRINT("I2C Read failed\n\r");
        return FAILURE;
    }
    return SUCCESS;
}


void inShootRange(int x1, int y1, int x2, int y2, int shootRadius){
    // x1 - my player's x position (center of circle)
    // y1 - my player's y position (center of circle)
    // x2 - other player's x position
    // y2 - other player's y position

    // Calculate the distance from the point to the center of the circle
    float distance = sqrt(pow(x2 - x1, 2) + pow(y2 - y1, 2));

    // Check if the distance is less than or equal to the radius - can shoot if so
    canShootFlag = distance <= shootRadius;
}


int ProcessWriteRegCommand(char *pcInpString) {
    unsigned char ucDevAddr, ucRegOffset, ucWrLen;
    unsigned char aucDataBuf[256];
    char *pcErrPtr;
    int iLoopCnt = 0;

    // Get the device address
    pcInpString = strtok(NULL, " ");
    RETERR_IF_TRUE(pcInpString == NULL);
    ucDevAddr = (unsigned char)strtoul(pcInpString+2, &pcErrPtr, 16);

    // Get the register offset to be written
    pcInpString = strtok(NULL, " ");
    RETERR_IF_TRUE(pcInpString == NULL);
    ucRegOffset = (unsigned char)strtoul(pcInpString+2, &pcErrPtr, 16);
    aucDataBuf[iLoopCnt] = ucRegOffset;
    iLoopCnt++;

    // Get the length of data to be written
    pcInpString = strtok(NULL, " ");
    RETERR_IF_TRUE(pcInpString == NULL);
    ucWrLen = (unsigned char)strtoul(pcInpString, &pcErrPtr, 10);

    // Get the bytes to be written
    for(; iLoopCnt < ucWrLen + 1; iLoopCnt++)
    {
        // Store the data to be written
        pcInpString = strtok(NULL, " ");
        RETERR_IF_TRUE(pcInpString == NULL);
        aucDataBuf[iLoopCnt] =
                (unsigned char)strtoul(pcInpString+2, &pcErrPtr, 16);
    }

    // Write the data values.
    RET_IF_ERR(I2C_IF_Write(ucDevAddr,&aucDataBuf[0],ucWrLen+1,1));

    UART_PRINT("I2C Write To address complete\n\r");

    return SUCCESS;
}


int ParseNProcessCmd(char *pcCmdBuffer) {
    char *pcInpString;
    int iRetVal = FAILURE;

    pcInpString = strtok(pcCmdBuffer, " \n\r");
    if(pcInpString != NULL)

    {
        if(!strcmp(pcInpString, "read"))
        {
            // Invoke the read command handler
            iRetVal = ProcessReadCommand(pcInpString);
        }
        else if(!strcmp(pcInpString, "readreg"))
        {
            // Invoke the readreg command handler
            iRetVal = ProcessReadRegCommand(pcInpString);
        }
        else if(!strcmp(pcInpString, "writereg"))
        {
            // Invoke the writereg command handler
            iRetVal = ProcessWriteRegCommand(pcInpString);
        }
        else if(!strcmp(pcInpString, "write"))
        {
            // Invoke the write command handler
            iRetVal = ProcessWriteCommand(pcInpString);
        }
        else
        {
            UART_PRINT("Unsupported command\n\r");
            return FAILURE;
        }
    }
    return iRetVal;
}

// Code for if we involve our own lives in our display
//void p1InitLifeDisplay(int numHearts) {
//    int xCoor = 121;
//
//    int i;
//    for(i = 0; i < numHearts; i++) {
//        drawHeart(xCoor, 115, BLUE);
//        xCoor = xCoor - 13;
//    }
//}
//
//
//void p1LifeDisplay(int numHearts) {
//    int xCoor = 121;
//    int numHeartsSubtract = maxLifeNum - numHearts;
//
//    int i;
//    for(i = 0; i < numHeartsSubtract; i++) {
//        drawHeart(xCoor, 115, GREEN);
//        xCoor = xCoor - 13;
//    }
//}

// Loads all the hearts on start of game play
void p2InitLifeDisplay(int numHearts) {
    int xCoor = 6;

    int i;
    for(i = 0; i < numHearts; i++) {
        drawHeart(xCoor, 4, RED);
        xCoor = xCoor + 13;
    }
}

// Life display of the opponent player
void p2LifeDisplay(int numHearts) {
    int xCoor = 6;
    int numHeartsSubtract = maxLifeNum - numHearts;

    int i;
    for(i = 0; i < numHeartsSubtract; i++) {
        drawHeart(xCoor, 4, GREEN);
        xCoor = xCoor + 13;
    }
}


// Post data to AWS
static int http_post(int iTLSSockID){
    char acSendBuff[512];
    char acRecvbuff[1460];
    char cCLLength[200];
    char* pcBufHeaders;
    int lRetVal = 0;

    pcBufHeaders = acSendBuff;
    // Set the POSTHEADER
    strcpy(pcBufHeaders, POSTHEADER);
    pcBufHeaders += strlen(POSTHEADER);
    strcpy(pcBufHeaders, HOSTHEADER);
    pcBufHeaders += strlen(HOSTHEADER);
    strcpy(pcBufHeaders, CHEADER);
    pcBufHeaders += strlen(CHEADER);
    strcpy(pcBufHeaders, "\r\n\r\n");

    int dataLength = strlen(stored);

    strcpy(pcBufHeaders, CTHEADER);
    pcBufHeaders += strlen(CTHEADER);
    strcpy(pcBufHeaders, CLHEADER1);

    pcBufHeaders += strlen(CLHEADER1);
    sprintf(cCLLength, "%d", dataLength);

    strcpy(pcBufHeaders, cCLLength);
    pcBufHeaders += strlen(cCLLength);
    strcpy(pcBufHeaders, CLHEADER2);
    pcBufHeaders += strlen(CLHEADER2);


    strcpy(pcBufHeaders, stored);

    pcBufHeaders += strlen(stored);

    int testDataLength = strlen(pcBufHeaders);

    UART_PRINT(acSendBuff);

    // Send the packet to the server
    lRetVal = sl_Send(iTLSSockID, acSendBuff, strlen(acSendBuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("POST failed. Error Number: %i\n\r",lRetVal);
        sl_Close(iTLSSockID);
        return lRetVal;
    }
    lRetVal = sl_Recv(iTLSSockID, &acRecvbuff[0], sizeof(acRecvbuff), 0);
    if(lRetVal < 0) {
        UART_PRINT("Received failed. Error Number: %i\n\r",lRetVal);
        return lRetVal;
    }
    else {
        acRecvbuff[lRetVal+1] = '\0';
        UART_PRINT(acRecvbuff);
        UART_PRINT("\n\r\n\r");
    }
    return 0;
}


// Sets the time to establish connection with AWS
static int set_time() {
    long retVal;

    g_time.tm_day = DATE;
    g_time.tm_mon = MONTH;
    g_time.tm_year = YEAR;
    g_time.tm_sec = HOUR;
    g_time.tm_hour = MINUTE;
    g_time.tm_min = SECOND;

    retVal = sl_DevSet(SL_DEVICE_GENERAL_CONFIGURATION,
                          SL_DEVICE_GENERAL_CONFIGURATION_DATE_TIME,
                          sizeof(SlDateTime),(unsigned char *)(&g_time));

    ASSERT_ON_ERROR(retVal);
    return SUCCESS;
}


void gameOverDisp(int playerNum) {
    fillScreen(BLACK);
    char declare[50];  // Create a character array to hold the formatted string
    positionedOutStr("Game Over!", 0, 50);
    sprintf(declare, "Player %d Won!", playerNum);  // Format the string
    positionedOutStr(declare, 0, 60);
}


int main() {
    unsigned long ulStatus;
    unsigned long ulUARTStatus;
    long lRetVal = -1;

    int iRetVal;
    BoardInit();

    PinMuxConfig();

    MAP_PRCMPeripheralClkEnable(PRCM_GSPI,PRCM_RUN_MODE_CLK);

    // Enable SysTick
    SysTickInit();

    // Base address for first timer
    g_ulBase = TIMERA0_BASE;

    // Configuring the timers
    Timer_IF_Init(PRCM_TIMERA0, g_ulBase, TIMER_CFG_PERIODIC, TIMER_A, 0);

    // Setup the interrupts for the timer timeouts
    Timer_IF_IntSetup(g_ulBase, TIMER_A, TimerBaseIntHandler);

    // Turn on the timers feeding values in 500 mSec

    //100 hz (cycles/sec) = 500 mSec
    Timer_IF_Start(g_ulBase, TIMER_A, 100);

    // Init UART
    PRCMPeripheralReset(PRCM_UARTA1);
    UARTConfigSetExpClk(UARTA1_BASE, PRCMPeripheralClockGet(PRCM_UARTA1), UART_BAUD_RATE, (UART_CONFIG_WLEN_8 | UART_CONFIG_STOP_ONE | UART_CONFIG_PAR_NONE));
    UARTIntRegister(UARTA1_BASE, UARTHandler); // handler is a function: check UART interrupt, clear it

    InitTerm();

    //clear status of uart
    ulUARTStatus = MAP_UARTIntStatus(UARTA1_BASE, true);
    UARTIntClear(UARTA1_BASE, ulUARTStatus);


    //connect tx and rx pins
    UARTFIFOLevelSet(UARTA1_BASE, UART_FIFO_TX1_8, UART_FIFO_RX1_8);
    UARTIntEnable(UARTA1_BASE, UART_INT_RX);

    //enabling uart
    UARTEnable(UARTA1_BASE);

    ClearTerm();

    // Register switch interrupt handlers
    MAP_GPIOIntRegister(switch2.port, GPIOA1IntHandler);
    MAP_GPIOIntRegister(switch3.port, GPIOA2IntHandler);

    ulStatus = MAP_GPIOIntStatus(switch2.port, false);
    MAP_GPIOIntClear(switch2.port, ulStatus);

    ulStatus = MAP_GPIOIntStatus(switch3.port, false);
    MAP_GPIOIntClear(switch3.port, ulStatus);           // clear interrupts on GPIOA2


    // I2C Init
    I2C_IF_Open(I2C_MASTER_MODE_FST);
    DisplayBanner(APP_NAME);
       DisplayUsage();

    Report("End of main.\n\r");

    // Register the interrupt handlers
    MAP_GPIOIntRegister(GPIOA0_BASE, GPIOIrHandler);

    // Configure rising edge interrupts on ir
    MAP_GPIOIntTypeSet(ir.port, ir.pin, GPIO_FALLING_EDGE);

    // Configure rising edge interrupts for sw3
    MAP_GPIOIntTypeSet(switch3.port, switch3.pin, GPIO_RISING_EDGE);
    MAP_GPIOIntTypeSet(switch2.port, switch2.pin, GPIO_RISING_EDGE);

    ulStatus = MAP_GPIOIntStatus(ir.port, false);
    MAP_GPIOIntClear(ir.port, ulStatus);

    // Clear global variables
    ir_intcount = 0;
    SW3_intcount=0;
    SW3_intflag=0;

    // Enable interrupts
    MAP_GPIOIntEnable(ir.port, ir.pin);
    MAP_GPIOIntEnable(switch3.port, switch3.pin);
    MAP_GPIOIntEnable(switch2.port, switch2.pin);

    // Initialize global default app configuration
    g_app_config.host = SERVER_NAME;
    g_app_config.port = GOOGLE_DST_PORT;

    // Connect the CC3200 to the local access point
    lRetVal = connectToAccessPoint();

    // Set time so that encryption can be used
    lRetVal = set_time();
    if(lRetVal < 0) {
        UART_PRINT("Unable to set time in the device");
        LOOP_FOREVER();
    }

    // Connect to the website with TLS encryption
    lRetVal = tls_connect();
    if(lRetVal < 0) {
        ERR_PRINT(lRetVal);
    }

//#if MASTER_MODE
//    Report("Before mastermain\n");
//    MasterMain();
//    Adafruit_Init();


   // Circle character's position
   int xCoor;
   int yCoor;
   int xCoor2;
   int yCoor2;
   int prevXCoor = 0;
   int prevYCoor = 0;
   int prevXCoor2 = 0;
   int prevYCoor2 = 0;
   int color = 0xFFFF;
   char endGame[5] = {'h', 'h', 'h', 'h', 'h'};
   signed char xAcceleration;
   signed char yAcceleration;
   int playerWon;
   const char *winner;
   MasterMain();
   Adafruit_Init();
   fillScreen(GREEN);
   setTextColor(BLACK,GREEN);

   // player two hearts
   p2InitLifeDisplay(maxLifeNum);


   while(FOREVER){
        // reset the countdown register
         SysTickReset();

         // wait for a fixed number of cycles
         UtilsDelay(2000);

         // read the countdown register and compute elapsed cycles
         uint64_t delta = SYSTICK_RELOAD_VAL - SysTickValueGet();

         // convert elapsed cycles to microseconds
         uint64_t delta_us = TICKS_TO_US(delta);
         playerScore += delta_us;

         // print measured time to UART
         //Report("cycles = %d\tus = %d\n\r", delta, delta_us);

         unsigned char ucDevAddr, ucXRefOffset, ucYRefOffset, ucRdLen;
         unsigned char aucRdDataBuf[256];

         // Define the address of the pin we are reading from
         ucDevAddr = 0x18;

         // The address of the pin with the x-axis reading
         ucXRefOffset = 0x3;

         // The address of the pin with the y-axis reading
         ucYRefOffset = 0x5;

         ucRdLen = 1;

         // Reading the X Coordinate
         RET_IF_ERR(I2C_IF_Write(ucDevAddr,&ucXRefOffset,1,0));

         // Read the specified length of data
         RET_IF_ERR(I2C_IF_Read(ucDevAddr, &aucRdDataBuf[0], ucRdLen));

         // Gets the acceleration on the y-axis based on the orientation of the physical OLED
         yAcceleration = aucRdDataBuf[0];

         // Reading the Y Coordinate
         RET_IF_ERR(I2C_IF_Write(ucDevAddr,&ucYRefOffset,1,0));

         RET_IF_ERR(I2C_IF_Read(ucDevAddr, &aucRdDataBuf[0], ucRdLen));  // Read the specified length of data

         // Gets the acceleration on the x-axis based on the orientation of the physical OLED
         xAcceleration = aucRdDataBuf[0];

         Report("p1Life: %d, p2life: %d \n\r", p1LifeCnt, p2LifeCnt);


         // Calculating the positional x and y values
         xCoor = xCoor + 0.5*(xAcceleration);
         yCoor = yCoor + 0.5*(yAcceleration);

         // Keeping the characters within range of the OLED display
         if(yCoor < 14+4 && xCoor < 64+4){ // Within the range of the top hearts
             yCoor = 14 + 4;
         }
         else if(xCoor > (127-4)){ // Checks if the ball is pass the edge: The OLED is 127 units wide and the ball is 4 units wide, hence subtraction
              xCoor = (127-4);
         }
         else if(yCoor > 110-4 && xCoor > 64-4) {
              yCoor = 110 - 4;
         }
         else if(xCoor < (0+4)){
             xCoor = (0+4);
         }
         if(yCoor>(127-4)){
             yCoor =(127-4);
         }
         else if(yCoor<(0+4)){
             yCoor =(0+4);
         }

         // Fill the previous position of the ball with black
         fillCircle(prevXCoor, prevYCoor, 4, GREEN);
         fillCircle(xCoor, yCoor, 4, BLUE);
         p2LifeDisplay(p2LifeCnt);

         // Checks if we are in range
         inShootRange(xCoor, yCoor, xCoor2, yCoor2, 10);

               if(canShootFlag == 1) {
                   Report("Can SHOOT!\n\r");
//                   UARTCharPut(UARTA1_BASE, p1LifeCnt);
//
//                    while(UARTCharsAvail(UARTA1_BASE)) {
//                        p2LifeCnt = (int) UARTCharGet(UARTA1_BASE);
//                    }
                   // Color the new position of the ball
                   fillCircle(xCoor, yCoor, 4, YELLOW);
               } else {
                   fillCircle(xCoor, yCoor, 4, BLUE);
               }

               MAP_UtilsDelay(800000);
//               if(p2LifeCnt == 0) {
//                   xCoor = 129;
//                   playerWon = 1;
//                   gameOverDisp(playerWon);
//               }

               UARTCharPut(UARTA1_BASE, xCoor);
               UARTCharPut(UARTA1_BASE, yCoor);

               prevXCoor = xCoor;
               prevYCoor = yCoor;
               while(UARTCharsAvail(UARTA1_BASE)) {

                       xCoor2 = (int) UARTCharGet(UARTA1_BASE);
                       yCoor2 = (int) UARTCharGet(UARTA1_BASE);

//                      Report("xCoor2: %d, yCoor2: %d \n", xCoor2, yCoor2);

                       // Checks if we hit the edge by seeing if we crossed any boundaries
                       if(yCoor2 < 14+4 && xCoor2 < 64+4){ // within the range of the top hearts
                          yCoor2 = 14 + 4;
                      }
                      else if(xCoor2 > (127-4)){ // Checks if the ball is pass the edge: The OLED is 127 units wide and the ball is 4 units wide, hence subtraction
                          xCoor2 = (127-4);
                      }
                      else if(yCoor2 > 110-4 && xCoor2 > 64-4) {
                          yCoor2 = 110 - 4;
                      }
                      else if(xCoor2 < (0+4)){
                          xCoor2 = (0+4);
                      }
                      if(yCoor2>(127-4)){
                          yCoor2 =(127-4);
                      }
                      else if(yCoor2<(0+4)){
                          yCoor2 =(0+4);
                      }

                       // Fill the previous position of the ball with black
                       fillCircle(prevXCoor2, prevYCoor2, 4, GREEN);


                       // Color the new position of the ball
                       fillCircle(xCoor2, yCoor2, 4, RED);

                       MAP_UtilsDelay(80000);

                       // Update coordinates
                       prevXCoor2 = xCoor2;
                       prevYCoor2 = yCoor2;
          }

           if(xCoor2 == 'h' && yCoor2 == 'h'){
               gameOverDisp(2);

               while(1){
                   Report("Game over\n\r");
               }
           }

     if (SW3_intflag) {
             SW3_intflag=0;  // clear flag
             if(canShootFlag) {
                 p2LifeCnt--;
             }

             //Checks if a player died after shoot button pressed
             if(p2LifeCnt == 0) {
                 int i;
                 for(i = 0; i < 5; i++) {
                     UARTCharPut(UARTA1_BASE, endGame[i]);
                 }
                Report("Score: %d", playerScore);

                     playerWon = 1;
                     winner = "Player 1";

                 // Send to AWS
                 // JSON format that gets sent to AWS
                     snprintf(stored, sizeof(stored),
                     "{" \
                         "\"state\": {\r\n"                                              \
                             "\"desired\" : {\r\n"                                       \
                                 "\"var\" : \""                                          \
                                     "Winner: %s, "                                      \
                                     "Score: %d"                                         \
                                 "\"\r\n"                                                \
                             "}"                                                         \
                         "}"                                                             \
                     "}\r\n\r\n",
                     winner, playerScore);

                 // Post the message from the CC3200 up to AWS
                 http_post(lRetVal);

                 gameOverDisp(playerWon);
             }
     }

//     char z;
//        if(p2LifeCnt == 0){
//            UARTCharPut(UARTA1_BASE, '0');
//            playerWon = 1;
//            gameOverDisp(playerWon);
//            break;
//        }//else{
//            while(UARTCharsAvail(UARTA1_BASE)) {
//               z = UARTCharGet(UARTA1_BASE);
//               if(z == '0'){
//                   playerWon = 2;
//                   gameOverDisp(playerWon);
//
//                   break;
//               }
//            }

//     while(UARTCharsAvail(UARTA1_BASE)) {
//          p1LifeCnt = (int) UARTCharGet(UARTA1_BASE);
//
//         if(p1LifeCnt == 0) {
//              playerWon = 2;
//              winner = "Player 2";
//              // Send to AWS
//             // JSON format that gets sent to AWS
//             snprintf(stored, sizeof(stored),"{" \
//                 "\"state\": {\r\n"                                              \
//                     "\"desired\" : {\r\n"                                       \
//                         "\"var\" :\""                                           \
//                             "Winner: "                                           \
//                             "%s"      \
//                             "\"\r\n"                                            \
//                     "}"                                                         \
//                 "}"                                                             \
//             "}\r\n\r\n", winner);
//
//             // Post the message from the CC3200 up to AWS
//             http_post(lRetVal);
//             gameOverDisp(playerWon);
//             break;
//         }
//     }

   }
}
//#else
//
//    SlaveMain();
//
//#endif


//*****************************************************************************
//
// Close the Doxygen group.
//! @}
//
//****************************************************************************
