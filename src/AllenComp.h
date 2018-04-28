/*************************
Copyright 2008 Jason Li

This file is part of ia2sat.

IA2SAT is free software; you can redistribute it
and/or modify it under the terms of the GNU General
Public License as published by the Free Software
Foundation; either version 2 of the License, or
(at your option) any later version.

IA2SAT is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the
implied warranty of MERCHANTABILITY or FITNESS FOR 
A PARTICULAR PURPOSE. See the GNU General Public 
License for more details.

You should have received a copy of the GNU General
Public License along with IA2SAT; if not, write to
the Free Software Foundation, Inc., 51 Franklin St, 
Fifth Floor, Boston, MA  02110-1301  USA
*************************/

/* Coding of Allen's relations */
/* coded as binary, assuming int  16bit or more */
#define REQ 		1
#define RLT 		2
#define RGT		4
#define RD		8
#define RDI		16
#define	RO		32
#define ROI		64
#define	RM		128
#define	RMI		256
#define	RS		512
#define	RSI		1024
#define RF		2048
#define	RFI		4096
#define DALL		8191

#define PA_DALL		7


/* Number of possible disjunctions (incl. 0) */
#define MAXSET		8192

/* Number of basic relations */
#define	MAXREL		13

#define PA_MAXREL 3

/* Allen Interval Algebra */

// Composition Table
RELTYPE	comp[MAXREL][MAXREL] = {
/*EQ*/	{REQ,RLT,RGT,RD,RDI,RO,
	 ROI,RM,RMI,RS,RSI,RF,RFI},
/*LT*/	{RLT, RLT, DALL,(RLT|RO|RM|RD|RS),RLT,RLT,(RLT|RO|RM|RD|RS),
	 RLT,(RLT|RO|RM|RD|RS),RLT,RLT,(RLT|RO|RM|RD|RS),RLT},
/*GT*/	{RGT,DALL,RGT,(RGT|ROI|RMI|RD|RF),RGT,(RGT|ROI|RMI|RD|RF),
	 RGT,(RGT|ROI|RMI|RD|RF),RGT,(RGT|ROI|RMI|RD|RF),RGT,RGT,RGT},
/*D*/	{RD,RLT,RGT,RD,DALL,(RLT|RO|RM|RD|RS),(RGT|ROI|RMI|RD|RF),RLT,RGT,
	 RD, (RGT|ROI|RMI|RD|RF),RD,(RLT|RO|RM|RD|RS)},
/*DI*/	{RDI,(RLT|RO|RM|RDI|RFI),(RGT|ROI|RDI|RMI|RSI),(RO|ROI|RD|RDI|REQ|RS|RSI|RF|RFI),
	 RDI,(RO|RDI|RFI),(ROI|RDI|RSI),(RO|RDI|RFI),(ROI|RDI|RSI),
	 (RO|RDI|RFI),RDI,(ROI|RDI|RSI),RDI},
/*O*/	{RO,RLT,(RGT|ROI|RDI|RMI|RSI),(RO|RD|RS),(RLT|RO|RM|RDI|RFI),
	 (RLT|RO|RM),(RO|ROI|RD|RDI|REQ|RS|RSI|RF|RFI),RLT,(ROI|RDI|RSI),RO,(RO|RDI|RFI),
	 (RO|RD|RS),(RLT|RO|RM)},
/*OI*/	{ROI,(RLT|RO|RM|RDI|RFI),RGT,(ROI|RD|RF),(RGT|ROI|RDI|RMI|RSI),
	 (RO|ROI|RD|RDI|REQ|RS|RSI|RF|RFI),(RGT|ROI|RMI),(RO|RDI|RFI),RGT,(ROI|RD|RF),
	 (RGT|ROI|RMI),ROI,(ROI|RDI|RSI)},
/*M*/	{RM,RLT,(RGT|ROI|RDI|RMI|RSI),(RO|RD|RS),RLT,RLT,(RO|RD|RS),
	 RLT,(RF|RFI|REQ),RM,RM,(RO|RD|RS),RLT},
/*MI*/	{RMI,(RLT|RO|RM|RDI|RFI),RGT,(ROI|RD|RF),RGT,(ROI|RD|RF),RGT,
	 (RS|RSI|REQ),RGT,(ROI|RD|RF),RGT,RMI,RMI},
/*S*/	{RS,RLT,RGT,RD,(RLT|RO|RM|RDI|RFI),(RLT|RO|RM),(ROI|RD|RF),RLT,
	 RMI,RS,(RS|RSI|REQ),RD,(RLT|RO|RM)},
/*SI*/	{RSI,(RLT|RO|RM|RDI|RFI),RGT,(ROI|RD|RF),RDI,(RO|RDI|RFI),ROI,
	 (RO|RDI|RFI),RMI,(RS|RSI|REQ),RSI,ROI,RDI},
/*F*/	{RF,RLT,RGT,RD,(RGT|ROI|RDI|RMI|RSI),(RO|RD|RS),(RGT|ROI|RMI),
	 RM,RGT,RD,(RGT|ROI|RMI),RF,(RF|RFI|REQ)},
/*FI*/	{RFI,RLT,(RGT|ROI|RDI|RMI|RSI),(RO|RD|RS),RDI,RO,(ROI|RSI|RDI),
	 RM,(ROI|RSI|RDI),RO,RDI,(RF|RFI|REQ),RFI}};
	 
RELTYPE pa_comp[PA_MAXREL][PA_MAXREL] = {
/*EQ*/ {REQ, RLT, RGT},
/*LT*/ {RLT, RLT, (REQ|RLT|RGT)}, 
/*GT*/ {RGT, (REQ|RLT|RGT), RGT}};

// The encode of 
int endPointLiteral[MAXREL][4] = {
/*EQ*/		{REQ, RLT, RGT, REQ},
/*LT*/		{RLT, RLT, RLT, RLT},
/*GT*/		{RGT, RGT, RGT, RGT},
/*D*/		{RGT, RLT, RGT, RLT},
/*DI*/		{RLT, RLT, RGT, RGT},
/*O*/		{RLT, RLT, RGT, RLT},
/*OI*/		{RGT, RLT, RGT, RGT},
/*M*/		{RLT, RLT, REQ, RLT},
/*MI*/		{RGT, REQ, RGT, RGT},
/*S*/		{REQ, RLT, RGT, RLT},
/*SI*/		{REQ, RLT, RGT, RGT},
/*F*/		{RGT, RLT, RGT, REQ},
/*FI*/		{RLT, RLT, RGT, REQ} };

