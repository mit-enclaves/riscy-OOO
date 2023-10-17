
// Copyright (c) 2017 Massachusetts Institute of Technology
// 
// Permission is hereby granted, free of charge, to any person
// obtaining a copy of this software and associated documentation
// files (the "Software"), to deal in the Software without
// restriction, including without limitation the rights to use, copy,
// modify, merge, publish, distribute, sublicense, and/or sell copies
// of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be
// included in all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
// EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
// MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
// NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
// BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

import FShow::*;
import GetPut::*;
import Vector::*;
import BuildVector::*;
import FIFO::*;
import Assert::*;

import Types::*;
import ProcTypes::*;
import CacheUtils::*;
import CCTypes::*;
import L2Tlb::*;
import MemLoader::*;
import CrossBar::*;
import MemLoader::*;

typedef struct {
    CoreId core;
    DmaMemReqId id;
    LineDataOffset dataSel;
} CoreDmaReqId deriving(Bits, Eq, FShow);

typedef union tagged {
    MemLoaderMemReqId MemLoader;
    CoreDmaReqId CoreDma;
} LLCDmaReqId deriving(Bits, Eq, FShow);

module mkLLCDmaConnect#(
    DmaServer#(LLCDmaReqId) llc,
    MemLoaderMemClient memLoader,
    Vector#(CoreNum, DmaMemClient) coreDma
)(Empty) provisos (
    Alias#(dmaRqT, DmaRq#(LLCDmaReqId))
);
    Bool verbose = True;

    // helper functions for cross bar
    function XBarDstInfo#(Bit#(0), Tuple2#(CoreId, DmaMemReq)) getDmaDst(CoreId core, DmaMemReq r);
        return XBarDstInfo {idx: 0, data: tuple2(core, r)};
    endfunction
    function Get#(DmaMemReq) dmaReqGet(DmaMemClient cli) = toGet(cli.memReq);

    // cross bar for CoreDma
    FIFO#(Tuple2#(CoreId, DmaMemReq)) coreDmaQ <- mkFIFO;
    mkXBar(getDmaDst, map(dmaReqGet, coreDma), vec(toPut(coreDmaQ)));

    function LineByteEn liftWordToLineByteEn(ByteEn be, LineDataOffset offset);
    // TODO check, potential mistake
        Bit#(TLog#(CacheLineSz)) newoffset = zeroExtend(offset) << 3; // sizeof(LineDataOffset) + 3
        LineByteEn res = replicate(False);
        for(Integer i = 0; i < valueof(NumBytes); i = i + 1) begin
            res[newoffset + fromInteger(i)] = be[i];
        end
        return res;
    endfunction
    
    function Line liftWordToLine(Data data, LineDataOffset offset);
        Line res = replicate(0);
        res[offset] = data;
        return res;
    endfunction

    // CoreDMA req is for a whole data
    function dmaRqT getCoreDmaReq(CoreId c, DmaMemReq r);
        LineDataOffset dataSel = ?;
        DmaMemReqId idx = ?;
        Addr addr = ?;
        LineByteEn byteEn = ?;
        Line data = ?;
        if(r matches tagged Tlb .req) begin
            dataSel = getLineDataOffset(req.addr);
            idx = Tlb (req.id);
            addr = req.addr;
            byteEn = replicate(False); // tlb req is always load
            data = ?;    
        end else if(r matches tagged ShrMem .req) begin
            dataSel = getLineDataOffset(req.addr);
            idx = ShrMem (req.id);
            addr = req.addr;
            byteEn = liftWordToLineByteEn(req.byteEn, dataSel); // secure shared memory can be store
            data = liftWordToLine(req.data, dataSel);    
        end
        
        let id = CoreDmaReqId {
            core: c,
            id: idx,
            dataSel: dataSel
        };
        return DmaRq {
            addr: addr,
            byteEn: byteEn,
            data: data,
            id: CoreDma (id)
        };
    endfunction

    // send req to LLC
    rule sendMemLoaderReqToLLC;
        memLoader.memReq.deq;
        let r = memLoader.memReq.first;
        dmaRqT req =  DmaRq {
            addr: r.addr,
            byteEn: r.byteEn,
            data: r.data,
            id: MemLoader (r.id)
        };
        llc.memReq.enq(req);
        if(verbose) begin
            $display("[LLCDmaConnnect sendMemLoaderReqToLLC] ",
                     fshow(r), " ; ", fshow(req));
        end
    endrule

    (* descending_urgency = "sendMemLoaderReqToLLC, sendCoreDmaReqToLLC" *)
    rule sendCoreDmaReqToLLC;
        let {c, r} <- toGet(coreDmaQ).get;
        let req = getCoreDmaReq(c, r);
        llc.memReq.enq(req);
        if(verbose) begin
            $display("  [LLCDmaConnnect sendCoreDmaReqToLLC] ", fshow(r), " ; ", fshow(req));
        end
    endrule

    // send Ld resp from LLC
    rule sendLdRespToMemLoader(llc.respLd.first.id matches tagged MemLoader .id);
        llc.respLd.deq;
        if(verbose) begin
            $display("[LLCDmaConnect sendLdRespToMemLoader] ",
                     fshow(llc.respLd.first));
        end
        doAssert(False, "No mem loader ld");
    endrule

    rule sendLdRespToCoreDma(llc.respLd.first.id matches tagged CoreDma .id);
        llc.respLd.deq;
        let resp = llc.respLd.first;
        if(id.id matches tagged Tlb .idx) begin
            let ld = TlbLdResp {
                data: resp.data[id.dataSel],
                id: idx
            };
            coreDma[id.core].respLd.enq(Tlb (ld));
            if(verbose) begin
                $display("  [LLCDmaConnect sendLdRespToCoreDma] ", fshow(resp), " ; ", fshow(ld));
            end
        end else if (id.id matches tagged ShrMem .idx) begin
            let ld = SharedLdResp {
                data: resp.data[id.dataSel],
                id: idx
            };
            coreDma[id.core].respLd.enq(ShrMem (ld));
            if(verbose) begin
                $display("  [LLCDmaConnect sendLdRespToCoreDma] ", fshow(resp), " ; ", fshow(ld));
            end
        end
    endrule

    // send St resp from LLC
    rule sendStRespToMemLoader(llc.respSt.first matches tagged MemLoader .id);
        llc.respSt.deq;
        memLoader.respSt.enq(id);
        if(verbose) begin
            $display("[LLCDmaConnect sendStRespToMemLoader] ",
                     fshow(llc.respSt.first));
        end
    endrule

    rule sendStRespToCoreDma(llc.respSt.first matches tagged CoreDma .id);
        llc.respSt.deq;
        if(verbose) begin
            $display("  [LLCDmaConnect sendStRespToCoreDma] ", fshow(llc.respSt.first));
        end
        // Nothing to do here
    endrule
endmodule
