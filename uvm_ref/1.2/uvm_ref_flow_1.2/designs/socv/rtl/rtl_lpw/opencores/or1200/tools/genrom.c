/*=======================================================================*/
/* Generate ROM from S-Format (4K byte)                                  */
/*-----------------------------------------------------------------------*/
/* Rev.1 August    14,2002 by Thorn Aitch                                */
/* Rev.2 September 22,2002 by Thorn Aitch : Modify Verilog Descriptions  */
/* Rev.3 October   07,2002 by Thorn Aitch : 4K byte version              */
/* Rev.4 January   21,2003 by Thorn Aitch : 8K byte + RAM signals        */
/*                                                                       */
/*(1) Usage:                                                             */
/*    genrom filename vfile datfile                                      */
/*        [filename]  : (Input ) Binary File Name of Motolora S-Format.  */
/*        vfile       : (Output) Verilog ROM description.                */
/*        datfile     : (Output) ROM data file.                          */
/*                                                                       */
/*(2) ROM Specification:                                                 */
/*    8192 byte (32bit x 2048word) : address = 00000000~00001FFF         */
/*=======================================================================*/

#include <stdio.h>
#include <string.h>
#include <malloc.h>
#include <stdlib.h>

#define ROMSIZE 32768 /* unit : byte */
#define MAXLINE 1000
#define MAXWORD 100


/*=============*/
/* main routine*/
/*=============*/
int main(int argc, char *argv[])
{
	FILE	*memFp;
	FILE	*romvFp;
	FILE	*romdFp;
	char	memLine[MAXLINE];
	char	hex[MAXWORD];
	char	*pMemLine, *pHex, *SkipSpace();
	int	i, errStx, recType, numCode;
	unsigned long	rom[ROMSIZE];
	unsigned long	addr;
	unsigned long data;

	if (argc != 5)
	{

 		printf("\n");
		printf("====================================\n");
		printf("==== Generate ROM from S-Format ====\n");
		printf("====================================\n");
		printf("[Command Usage]\n");
		printf("    genrom filename vfile datfile\n");
		printf("\n");
		printf("        [filename] : (input ) Binary File Name of Motorola S-Format.\n");
		printf("        vfile      : (output) Verilog ROM description.\n");
		printf("        datfile    : (output) ROM data file for $readmemh.\n");
		printf("        module_nm  : verilog module name of the rom.\n");
		printf("\n");
		printf("[ROM Specification]\n");
		printf("    -32768 byte (32bit x 8192word)\n");
		printf("    -module rom(CLK, CE, WE, SEL, ADR, DATI, DATO);\n");
		printf("        input  CLK;         : clock\n");
		printf("        input  CE;          : chip enable\n");
        printf("        input  WE;          : write enable (ignored)\n");
        printf("        input  [ 3:0] SEL;  : byte lane (ignored)\n");
		printf("        input  [14:0] ADR;  : address input\n");
        printf("        input  [31:0] DATI; : data input (ignored)\n");
		printf("        output [31:0] DATO; : data output\n");
		printf("    -CE and ADR are latched at posedge of CLK,\n");
		printf("    -From the negedge of CLK, DAT will be out.\n");
		printf("    -If CE is 0, DAT will be 32'h00000000.\n");
		printf("    -ADR[1:0] are ignored.\n");
		printf("\n");
		return(1);
	}

	/*------------------*/
	/* initialize rom[] */
	/*------------------*/
	for (i = 0 ; i < ROMSIZE ; i++)
	{
		rom[i] = 255; /* init values are all FF */
	}

	/*-----------------------------*/
	/* read s-format file to rom[] */
	/*-----------------------------*/
	if ((memFp = fopen(argv[1], "r")) == NULL)
	{
 		printf("ERROR:cant open the file.\n");
		return(2);
	}
	errStx = 0;
	pHex = hex;
	while (fgets(memLine, MAXLINE, memFp) != NULL)
	{
		pMemLine = memLine;
		pMemLine = SkipSpace(pMemLine);

		if (*pMemLine++ != 'S') /* start mark ? */
		{
			errStx = 1;
			break;
		}

		if ((*pMemLine == '0') || (*pMemLine == '5')) continue;	/* if comment ? */

		if (*pMemLine == '1') recType = 1;						/* record type */
		else if (*pMemLine == '2') recType = 2;
		else if (*pMemLine == '3') recType = 3;
		else if (*pMemLine == '7') break;
		else if (*pMemLine == '8') break;
		else if (*pMemLine == '9') break;
		else
		{
		errStx = 1;
		break;
		}
		pMemLine++;

		pHex = strncpy(pHex,pMemLine,2);				/* the number of code */
		pMemLine = pMemLine + 2;
		*(pHex + 2) = '\0';
		if ((ChkHex(pHex) == 0) || (sscanf(pHex,"%X",&numCode) == EOF))
		{
			errStx = 1;
			break;
		}

		if (recType == 1)								/* load address */
		{
			pHex = strncpy(pHex,pMemLine,4);
			pMemLine = pMemLine + 4;
			numCode = numCode - 2;
			*(pHex + 4) = '\0';
			if (strlen(pHex) != 4)
			{
				errStx = 1;
				break;
			}
		}
		if (recType == 2)
		{
			pHex = strncpy(pHex,pMemLine,6);
			pMemLine = pMemLine + 6;
			numCode = numCode - 3;
			*(pHex + 6) = '\0';
			if (strlen(pHex) != 6)
			{
				errStx = 1;
				break;
			}
		}
		if (recType == 3)
		{
			pHex = strncpy(pHex,pMemLine,8);
			pMemLine = pMemLine + 8;
			numCode = numCode - 4;
			*(pHex + 8) = '\0';
			if (strlen(pHex) != 8)
			{
				errStx = 1;
				break;
			}
		}

		if ((ChkHex(pHex) == 0) || (sscanf(pHex,"%lX",&addr) == EOF))
		{
			errStx = 1;
			break;
		}

		for (i = 0 ; i < numCode - 1 ; i++)				/* code */
		{
			pHex = strncpy(pHex,pMemLine,2);
			pMemLine = pMemLine + 2;
			*(pHex + 2) = '\0';
			if (strlen(pHex) != 2)
			{
				errStx = 1;
				break;
			}
			if ((ChkHex(pHex) == 0) || (sscanf(pHex,"%X",&data) == EOF))
			{
				errStx = 1;
				break;
			}
			if (addr <= ROMSIZE)
			{
				rom[addr] = data;
				addr++;
			}
			else
			{
				errStx = 2;
				break;
			}
		}
		if (errStx != 0) break;
	}

	if (errStx == 1)
	{ 
		printf("ERROR:syntax error in object file.\n");
		return(2);
	}
	if (errStx == 2)
	{
		printf("ERROR:rom address out of range.\n");
		return(2);
	}
	if (fclose(memFp) == EOF)
	{
 		printf("ERROR:file close error.\n");
		return(2);
	}

	/*--------------------*/
	/* write verilog file */
	/*--------------------*/
	if ((romvFp = fopen(argv[2], "w")) == NULL)
	{
 		printf("ERROR:cant open %s for writing\n", argv[2]);
		return(3);
	}

    fprintf(romvFp, "//--------------------\n");
	fprintf(romvFp, "// Verilog ROM : %s\n", argv[2]);
    fprintf(romvFp, "//--------------------\n");
	fprintf(romvFp, "// ROM Specification\n");
	fprintf(romvFp, "//    -32768 byte (32bit x 8192 word)\n");
	fprintf(romvFp, "//    -module %s(CLK, CE, WE, SEL, ADR, DATI, DATO);\n", argv[4]);
	fprintf(romvFp, "//        input  CLK;         : clock\n");
	fprintf(romvFp, "//        input  CE;          : chip enable\n");
    fprintf(romvFp, "//        input  WE;          : write enable (ignored)\n");
    fprintf(romvFp, "//        input  [ 3:0] SEL;  : byte lane (ignored)\n");
	fprintf(romvFp, "//        input  [14:0] ADR;  : address input\n");
    fprintf(romvFp, "//        input  [31:0] DATI; : data input (ignored)\n");
	fprintf(romvFp, "//        output [31:0] DATO; : data output\n");
	fprintf(romvFp, "//    -CE and ADR are latched at posedge of CLK,\n");
	fprintf(romvFp, "//    -From the negedge of CLK, DAT will be out.\n");
	fprintf(romvFp, "//    -If CE is 0, DAT will be 32'h00000000.\n");
	fprintf(romvFp, "//    -ADR[1:0] are ignored.\n");
	fprintf(romvFp, "\n");
    fprintf(romvFp, "`include \"timescale.v\"\n");
	fprintf(romvFp, "\n");
	fprintf(romvFp, "module %s (CLK, CE, WE, SEL, ADR, DATI, DATO);\n", argv[4]);
	fprintf(romvFp, "    input  CLK, CE, WE;\n");
	fprintf(romvFp, "    input  [ 3:0] SEL;\n");
	fprintf(romvFp, "    input  [14:0] ADR;\n");
	fprintf(romvFp, "    input  [31:0] DATI;\n");
	fprintf(romvFp, "    output [31:0] DATO;\n");
	fprintf(romvFp, "\n");
	fprintf(romvFp, "    reg [31:0] DATO;\n");
	fprintf(romvFp, "\n");
	fprintf(romvFp, "    always @(negedge CLK) begin\n");
	fprintf(romvFp, "        if (CE == 1'b0)\n");
	fprintf(romvFp, "            DATO <= 32'h00000000;\n");
	fprintf(romvFp, "        else\n");
	fprintf(romvFp, "            begin\n");
	fprintf(romvFp, "                case(ADR[14:2])\n");
	
	for (i = 0 ; i < ROMSIZE / 4 ; i++)
	{
	fprintf(romvFp, "                    13'h%03X : DATO <= 32'h", i);
	fprintf(romvFp, "%02X", rom[i*4]);
	fprintf(romvFp, "%02X", rom[i*4+1]);
	fprintf(romvFp, "%02X", rom[i*4+2]);
	fprintf(romvFp, "%02X;\n", rom[i*4+3]);
	}

	fprintf(romvFp, "                    default : DATO <= 32'hxxxxxxxx;\n");
	fprintf(romvFp, "                endcase\n");
	fprintf(romvFp, "            end\n");
	fprintf(romvFp, "    end\n");
	fprintf(romvFp, "endmodule\n");

	if (fclose(romvFp) == EOF)
	{
 		printf("ERROR:file close error.\n");
		return(3);
	}

	/*-----------------*/
	/* write data file */
	/*-----------------*/
	if ((romdFp = fopen(argv[3], "w")) == NULL)
	{
 		printf("ERROR:cant open file %s for writing\n", argv[3]);
		return(4);
	}

	for (i = 0 ; i < ROMSIZE ; i = i + 4)
	{
		fprintf(romdFp, "%02X", rom[i]);
		fprintf(romdFp, "%02X", rom[i + 1]);
		fprintf(romdFp, "%02X", rom[i + 2]);
		fprintf(romdFp, "%02X", rom[i + 3]);
		/* fprintf(romdFp, " %d", i); [DEBUG] */
		fprintf(romdFp, "\n");
	}

	if (fclose(romdFp) == EOF)
	{
 		printf("ERROR:file close error.\n");
		return(4);
	}

	/*-----------------------------------------*/
	return(0);
}

/*============*/
/* skip space */
/*============*/
char *SkipSpace(pStr)
	char	*pStr;
{
	while(isspace((int) *pStr)) pStr++;
	return(pStr);
}

/*===========*/
/* check hex */
/*===========*/
int ChkHex(str)
	char	*str;
{
	int		result;
	
	result = 0;
	while(*str != '\0')
	{
		result = isxdigit(*(str++));
		if (result == 0) break;
	}
	return(result);
}

/* end of source file */


