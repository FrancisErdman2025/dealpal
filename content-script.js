// content-script.js - optional persistent product extraction helper
(function(){
  // simple run-once extractor (not injected by default)
  function extract() {
    const title = document.querySelector('h1')?.innerText || document.title;
    const priceEl = document.querySelector('.price, [itemprop="price"], .priceblock_ourprice, .a-price .a-offscreen');
    const price = priceEl ? (priceEl.innerText || priceEl.textContent).trim() : null;
    const payload = { title, priceText: price, price: price ? parseFloat(price.replace(/[^\d\.]/g,'')) : null, url: location.href, ts: Date.now() };
    chrome.runtime.sendMessage({ type: 'PRODUCT_INFO', payload });
  }
  // run once
  extract();
})();
